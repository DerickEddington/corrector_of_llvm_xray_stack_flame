use std::collections::VecDeque;


pub struct ErrorCapturingIterator<I, E> {
    iter:   I,
    errors: VecDeque<E>,
}

impl<I, T, E> ErrorCapturingIterator<I, E>
where
    I: Iterator<Item = Result<T, E>>,
{
    pub fn new(iter: I) -> Self { Self { iter, errors: VecDeque::new() } }

    pub fn status(&mut self) -> Result<(), E> {
        match self.errors.pop_front() {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
}

impl<I, T, E> Iterator for ErrorCapturingIterator<I, E>
where
    I: Iterator<Item = Result<T, E>>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(Ok(next)) => Some(next),
            Some(Err(error)) => {
                self.errors.push_back(error);
                None
            },
            None => None,
        }
    }
}


#[cfg(test)]
mod tests {
    use {super::*, std::fmt::Debug};

    #[test]
    fn basic() {
        fn assert_captured<const SN: usize, const ECN: usize, T: Debug + Eq, E: Debug + Eq>(
            seq: [Result<T, E>; SN],
            expected_collected: [T; ECN],
            expected_status: Result<(), E>,
        ) {
            let eci = &mut ErrorCapturingIterator::new(seq.into_iter());
            let collected: Vec<T> = eci.collect();
            assert_eq!(collected, expected_collected);
            assert_eq!(eci.status(), expected_status);
        }

        assert_captured::<0, 0, (), ()>([], [], Ok(()));
        assert_captured([Ok::<_, ()>(1)], [1], Ok(()));
        assert_captured([Ok(1), Err("oops"), Ok(2)], [1], Err("oops"));
        assert_captured([Err("oops"), Ok(1), Ok(2)], [], Err("oops"));
        assert_captured(
            [
                Ok(1),
                Ok(2),
                Ok(3),
                Err(['b', 'a', 'i', 'l']),
                Ok(5),
                Err(['o', 'o', 'p', 's']),
                Ok(7),
            ],
            [1, 2, 3],
            Err(['b', 'a', 'i', 'l']),
        );
    }
}
