use {crate::{bad_tree::BadTree,
             good_tree::GoodTree,
             node::{Attribute as NodeAttribute, Node, Path as NodePath, Ref as NodeRef},
             record::Record,
             tree::{OrdRecord, Tree}},
     std::error::Error};

mod error_capturing_iterator;

type CPUtimeStampCounter = u64;


fn main() -> Result<(), Box<dyn Error>> {
    use {error_capturing_iterator::ErrorCapturingIterator,
         std::{io::{self, BufRead as _, BufWriter},
               str::FromStr as _}};

    let (stdin, mut stdout) = (io::stdin().lock(), BufWriter::new(io::stdout().lock()));

    let input_lines = stdin.lines().map(|result| result.map_err(Box::<dyn Error>::from));

    // The input is assumed to have bad/incorrect values due to the `llvm-xray` bug.
    let input_records_assumed_bad = input_lines.map(|line_result| {
        line_result.and_then(|line| Record::from_str(&line).map_err(Box::<dyn Error>::from))
    });
    // Because the input lines might cause errors due to invalid UTF-8 or due to invalid syntax
    // format, we capture any errors during the iteration.  This avoids reading all of the input
    // at once (just to check for error), so that instead the iteration more efficiently drives
    // the reading iteratively or stops on the first error during iteration.
    let mut input = ErrorCapturingIterator::new(input_records_assumed_bad);

    let bad_tree = BadTree::from_iter(&mut input);
    let status = input.status();

    if status.is_ok() {
        let good_tree = bad_tree.correct()?;
        good_tree.dump(&mut stdout)?;
    }

    status
}


mod record {
    use {crate::{NodeAttribute, NodePath},
         std::{fmt::{self, Display, Formatter},
               str::FromStr}};

    /// Representation of a line of the format that is the input to `flamegraph.pl` and that is
    /// output by `llvm-xray stack --stack-format=flame`.
    #[derive(Debug, Default, Eq, PartialEq)]
    pub struct Record {
        pub node_path: NodePath,
        pub attribute: NodeAttribute,
    }

    /// Parse a line of the format into our internal representation.
    impl FromStr for Record {
        type Err = &'static str;

        fn from_str(line: &str) -> Result<Self, Self::Err> {
            const ERROR: &str = "invalid flame format line";
            let mut components: Vec<String> = line.split(';').map(String::from).collect();
            if components.len() >= 2 {
                let attr_str = components.pop().ok_or(ERROR)?;
                let attribute = attr_str.trim().parse().map_err(|_| ERROR)?;
                Ok(Self { node_path: components, attribute })
            } else {
                Err(ERROR)
            }
        }
    }

    /// Write the textual representation as a line of the format.
    impl Display for Record {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "{}; {}", self.node_path.join(";"), self.attribute)
        }
    }

    #[cfg(test)]
    mod tests {
        use {super::*, crate::CPUtimeStampCounter};

        #[test]
        fn basic() {
            fn assert_ok(line: &str, expected: Record) {
                let result: Result<Record, _> = line.parse();
                assert_eq!(result, Ok(expected));
                let record: Record = result.unwrap();
                assert_eq!(format!("{}", record), line);
            }

            assert_ok("foo; 1", Record { node_path: vec!["foo".to_string()], attribute: 1 });
            assert_ok("bar;zab; 2", Record {
                node_path: ["bar".into(), "zab".into()].into(),
                attribute: 2,
            });
            assert_ok("a;b r;aca;da\nbr;a; 18446744073709551615", Record {
                node_path: ["a", "b r", "aca", "da\nbr", "a"]
                    .into_iter()
                    .map(String::from)
                    .collect(),
                attribute: CPUtimeStampCounter::MAX,
            });

            let error: Result<Record, _> = Err("invalid flame format line");
            assert_eq!("".parse(), error);
            assert_eq!("a".parse(), error);
            assert_eq!("0".parse(), error);
            assert_eq!("foo 1".parse(), error);
            assert_eq!("bar;zab 2".parse(), error);
            assert_eq!("a; -1".parse(), error);
            assert_eq!("a; 18446744073709551616".parse(), error);
        }
    }
}


mod node {
    use {crate::CPUtimeStampCounter,
         std::{cell::Cell,
               collections::{hash_map::Entry, HashMap},
               rc::Rc}};

    pub type Name = String; // TODO: change to Rc<str> cons'ed from global interned table
    pub type Path = Vec<Name>;
    pub type Attribute = CPUtimeStampCounter;
    pub type Ref = Rc<Node>;

    #[derive(Default)]
    pub struct Node {
        pub kind:      Cell<Kind>,
        pub attribute: Cell<Option<Attribute>>,
    }

    #[derive(Default)]
    pub enum Kind {
        #[default]
        Leaf,
        Branch {
            children: HashMap<Name, Ref>,
        },
    }

    impl Node {
        /// The purpose of the entire program.
        pub fn correct_for_child(&self, child: &Self) {
            if let Some(attr) = self.attribute.get() {
                let child_attr = child.attribute.get().expect("accounted for");
                self.attribute.set(Some(attr.saturating_sub(child_attr)));
            }
        }

        /// Return the `name`d child, creating it if it's not already present.
        pub fn child(&self, name: &Name) -> Ref {
            let kind = self.kind.take();
            match kind {
                Kind::Leaf => {
                    self.kind.set(Kind::Branch { children: HashMap::new() });
                    self.child(name)
                },
                Kind::Branch { mut children } => {
                    let child_ref = match children.entry(name.clone()) {
                        Entry::Occupied(entry) => {
                            let already_present_child = entry.get();
                            Ref::clone(already_present_child)
                        },
                        Entry::Vacant(entry) => {
                            let newly_created_child = Ref::default();
                            Ref::clone(entry.insert(newly_created_child))
                        },
                    };
                    self.kind.set(Kind::Branch { children });
                    child_ref
                },
            }
        }

        pub fn for_each_child<E>(
            &self,
            mut f: impl FnMut(&Self, &Self) -> Result<(), E>,
        ) -> Result<(), E> {
            match self.kind.take() {
                Kind::Leaf => self.kind.set(Kind::Leaf),
                Kind::Branch { children } => {
                    for child in children.values() {
                        f(self, child)?;
                    }
                    self.kind.set(Kind::Branch { children });
                },
            }
            Ok(())
        }
    }
}


mod tree {
    use {crate::{NodeRef, Record},
         std::{cmp::Ordering, collections::BTreeMap}};

    #[derive(Eq)]
    pub struct OrdRecord {
        pub ordinal: usize,
        pub record:  Record,
    }

    impl PartialEq for OrdRecord {
        fn eq(&self, other: &Self) -> bool {
            debug_assert_eq!(self.record, other.record);
            self.ordinal == other.ordinal
        }
    }
    impl PartialOrd for OrdRecord {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(Ord::cmp(self, other)) }
    }
    impl Ord for OrdRecord {
        fn cmp(&self, other: &Self) -> Ordering { Ord::cmp(&self.ordinal, &other.ordinal) }
    }

    #[derive(Default)]
    pub struct Tree {
        pub roots:          NodeRef,
        pub original_order: BTreeMap<OrdRecord, NodeRef>,
    }
}


mod bad_tree {
    use {crate::{GoodTree, Node, NodeRef, OrdRecord, Record, Tree},
         std::error::Error};

    /// FlameGraph data which is incorrect such that each non-leaf node (which represents a
    /// function in a call-stack) has its total time including the times of its children
    /// (functions called by it).
    pub struct BadTree(Tree);

    /// The only way to construct a tree from an input.  Assumes all inputs are bad and need to be
    /// corrected, which is the point of this program.
    impl FromIterator<Record> for BadTree {
        fn from_iter<T: IntoIterator<Item = Record>>(bad: T) -> Self {
            let mut bad_tree = BadTree(Tree::default());
            bad_tree.extend(bad);
            bad_tree
        }
    }

    impl Extend<Record> for BadTree {
        fn extend<T: IntoIterator<Item = Record>>(&mut self, input: T) {
            let tree = &mut self.0;

            let base_ordinal =
                tree.original_order.last_key_value().map_or(0, |(k, _v)| k.ordinal + 1);
            debug_assert!(!tree.original_order.contains_key({
                let dummy = Record::default();
                &OrdRecord { ordinal: base_ordinal, record: dummy }
            }));

            for (ordinal, record) in
                input.into_iter().enumerate().map(|(o, r)| (base_ordinal + o, r))
            {
                let mut parent = NodeRef::clone(&tree.roots);
                if let Some((last_component, path_prefix)) = record.node_path.split_last() {
                    for component in path_prefix {
                        parent = parent.child(component);
                    }
                    let last_node = parent.child(last_component);

                    match last_node.attribute.take() {
                        // Reoccurrence of this node path.
                        Some(attr) => {
                            let summed_attrs =
                                attr.checked_add(record.attribute).expect("no overflow");
                            last_node.attribute.set(Some(summed_attrs));
                            // Don't insert into `tree.original_order`, because this node already
                            // was inserted the first time.  This prevents having reoccurrences in
                            // our dump, which is necessary because our corrected attribute is the
                            // sum of all original reoccurrences' attributes.
                        },
                        // First occurrence of this node path.
                        None => {
                            // So it can be corrected later.
                            last_node.attribute.set(Some(record.attribute));
                            let prior = tree
                                .original_order
                                .insert(OrdRecord { ordinal, record }, last_node);
                            // These ordinals are guaranteed to be unique.
                            debug_assert!(prior.is_none());
                        },
                    }
                }
            }
        }
    }

    impl BadTree {
        /// The primary operation of this program.
        pub fn correct(self) -> Result<GoodTree, Box<dyn Error>> {
            fn recur(parent: &Node, child: &Node) -> Result<(), Box<dyn Error>> {
                // This relies on using a child's incorrect value while it's its total
                // time (before correcting the child's time next).
                parent.correct_for_child(child);
                // Now correct this child's time (after we used the incorrect value).
                child.for_each_child(recur)?;
                Ok(())
            }
            let tree = self.0;
            tree.roots.for_each_child(|_, root| root.for_each_child(recur))?;
            Ok(GoodTree(tree))
        }
    }
}


mod good_tree {
    use {crate::{Record, Tree},
         std::{io, io::Write}};

    /// FlameGraph data which has been corrected such that each non-leaf node (which represents a
    /// function in a call-stack) has only its time spent directly in itself excluding the times
    /// of its children (functions called by it).
    pub struct GoodTree(pub Tree);

    impl GoodTree {
        /// Yields the corrected records in the same order as the original input.
        pub fn iter(&self) -> impl Iterator<Item = Record> + '_ {
            let tree = &self.0;
            tree.original_order.iter().map(|(ord_record, node)| {
                let original_node_path = &ord_record.record.node_path;
                let possibly_corrected_attribute =
                    node.attribute.get().expect("these nodes always have");
                Record {
                    node_path: original_node_path.clone(),
                    attribute: possibly_corrected_attribute,
                }
            })
        }

        /// Write the textual representation of all the corrected records as an entire file of
        /// lines of the flame-graph format as UTF-8.
        ///
        /// This outputs to a `Write`r so that it's more flexible in where the dump can go
        /// efficiently.
        pub fn dump(&self, out: &mut impl Write) -> io::Result<()> {
            for record in self.iter() {
                out.write_all(record.to_string().as_bytes())?;
                out.write_all("\n".as_bytes())?;
            }
            out.flush()?;
            Ok(())
        }
    }
}


#[cfg(test)]
mod tests {
    use {super::*, std::str::FromStr};

    #[test]
    fn basic() {
        #[rustfmt::skip]
        const BAD: &str = "\
          thread1;main; 5925054742\n\
          thread1;main;f2; 5925051360\n\
          thread1;main;f2;busy; 5925047168\n\
          thread1;main; 5941982261\n\
          thread1;main;f1; 5941978880\n\
          thread1;main;f1;busy; 5941971904\n\
          thread1;main; 5930717973\n\
          thread1;main;busy; 5930714592\n\
        ";
        #[rustfmt::skip]
        const GOOD: &str = "\
          thread1;main; 10144\n\
          thread1;main;f2; 4192\n\
          thread1;main;f2;busy; 5925047168\n\
          thread1;main;f1; 6976\n\
          thread1;main;f1;busy; 5941971904\n\
          thread1;main;busy; 5930714592\n\
        ";

        let bad = BAD.lines().map(|line| Record::from_str(line).unwrap());
        let bad_tree = BadTree::from_iter(bad);

        let good_tree = bad_tree.correct().unwrap();
        let good_dump = {
            let mut output = Vec::new();
            assert!(good_tree.dump(&mut output).is_ok());
            String::from_utf8(output).unwrap()
        };

        assert_eq!(good_dump, GOOD);
    }
}
