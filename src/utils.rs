use either::Either::{self, Left, Right};
use permutations::Permutation;
use rand::{distributions::Uniform, prelude::Distribution};
use std::fmt::Debug;

pub fn is_unique<T: Eq + std::hash::Hash>(s: &[T]) -> bool {
    let mut uniq = std::collections::HashSet::with_capacity(s.len());
    s.iter().all(|cur| uniq.insert(cur))
}

pub trait EitherExt<T, U> {
    fn bimap<V, W>(self, f1: impl Fn(T) -> V, f2: impl Fn(U) -> W) -> impl EitherExt<V, W>;
    fn join<V>(self, f1: impl Fn(T) -> V, f2: impl Fn(U) -> V) -> V;
}

impl<T, U> EitherExt<T, U> for Either<T, U> {
    fn bimap<V, W>(self, f1: impl Fn(T) -> V, f2: impl Fn(U) -> W) -> Either<V, W> {
        match self {
            Left(t) => Left(f1(t)),
            Right(u) => Right(f2(u)),
        }
    }

    fn join<V>(self, f1: impl Fn(T) -> V, f2: impl Fn(U) -> V) -> V {
        match self {
            Left(t) => f1(t),
            Right(u) => f2(u),
        }
    }
}

pub fn represents_id(arr: &[usize]) -> bool {
    (0..arr.len()).eq(arr.iter().cloned())
}

pub fn argmax<T: Ord>(s: &[T]) -> Option<usize> {
    s.iter().enumerate().max_by_key(|x| x.1).map(|(idx, _)| idx)
}

pub fn remove_multiple<T>(me: &mut Vec<T>, mut to_remove: Vec<usize>) {
    to_remove.sort_unstable();
    to_remove.reverse();
    for r in to_remove {
        me.remove(r);
    }
}

pub fn necessary_permutation<T: Eq>(side_1: &[T], side_2: &[T]) -> Result<Permutation, String> {
    let n1 = side_1.len();
    let n2 = side_2.len();
    if n1 != n2 {
        return Err(format!(
            "No permutation can take side 1 to side 2 because the lengths {} and {} don't match",
            n1, n2
        ));
    }
    let mut trial_perm = Vec::<usize>::with_capacity(n1);
    for cur in side_1 {
        let Some(idx) = side_2.iter().position(|t| *t == *cur) else {
            return Err("No permutation can take side 1 to side 2 \
            because an item in side 1 was not in side 2"
                .to_string());
        };
        trial_perm.push(idx);
    }
    Permutation::try_from(trial_perm)
        .map_err(|_| {
            "No permutation can take side 1 to side 2\n\
            because there were multiple in side 1 that were equal \
            and so mapped to the same index in side 2"
                .to_string()
        })
        .map(|e| e.inv())
}

fn perm_decompose(p: &Permutation) -> Vec<(usize, usize)> {
    if p.len() <= 1 {
        return vec![];
    }
    let mut seen = vec![false; p.len()];
    let mut answer = Vec::with_capacity(p.len() - 1);
    for i in 0..p.len() {
        if !seen[i] {
            seen[i] = true;
            let mut j = p.apply(i);
            let mut j_before = i;
            while j != i {
                answer.push((j_before, j));
                seen[j] = true;
                j_before = j;
                j = p.apply(j_before);
            }
        }
    }
    answer
}

pub fn in_place_permute<T>(me: &mut [T], p: &Permutation) {
    let transpositions = perm_decompose(p);
    for (p, q) in transpositions {
        me.swap(p, q);
    }
}

#[allow(dead_code)]
pub fn rand_perm(n: usize, max_depth: usize) -> Permutation {
    let mut rng = rand::thread_rng();
    let between = Uniform::from(0..n);
    let mut answer = Permutation::identity(n);
    for _ in 0..max_depth {
        let i = between.sample(&mut rng);
        let j = between.sample(&mut rng);
        answer = answer * Permutation::transposition(n, i, j);
    }
    answer
}

pub trait ResultExt<T, E> {
    fn zip<U>(self, other: Result<U, E>) -> Result<(T, U), E>;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    // combines the values to tuple
    fn zip<U>(self, other: Result<U, E>) -> Result<(T, U), E> {
        match (self, other) {
            (Ok(a), Ok(b)) => Ok((a, b)),
            (Err(e), _) | (_, Err(e)) => Err(e),
        }
    }
}

#[allow(dead_code)]
pub fn test_asserter<T, U, F>(
    observed: Result<T, U>,
    expected: Result<T, U>,
    aux_test: F,
    equation_str: &str,
) where
    F: Fn(&T, &T) -> bool,
    T: Debug + PartialEq,
{
    let Ok((real_observed, real_expected)) = observed.zip(expected) else {
        panic!(
            "Error on one of observed/expected sides when checking {:?}",
            equation_str
        )
    };

    assert!(aux_test(&real_observed, &real_expected));
    assert!(
        real_observed == real_expected,
        "{:?} vs {:?} when checking {:?}",
        real_observed,
        real_expected,
        equation_str
    );
}

#[macro_export]
macro_rules! assert_ok {
    ( $x:expr ) => {
        match $x {
            std::result::Result::Ok(v) => v,
            std::result::Result::Err(e) => {
                panic!("Error calling {}: {:?}", stringify!($x), e);
            }
        }
    };
}

mod test {

    #[test]
    fn nec_permutation() {
        use crate::utils::{necessary_permutation, rand_perm};
        use rand::{distributions::Uniform, prelude::Distribution};
        let n_max = 10;
        let between = Uniform::<usize>::from(2..n_max);
        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let n = between.sample(&mut rng);
            let set = (0..n).map(|i| format!("{}", i)).collect::<Vec<String>>();
            let p1 = rand_perm(n, n * n / 4);
            let permuted_set = p1.permute(&set);
            let found_perm = necessary_permutation(&set, &permuted_set);
            assert_eq!(found_perm, Ok(p1));
        }
    }

    #[test]
    fn perm_decompose() {
        use crate::utils::{perm_decompose, rand_perm};
        use permutations::Permutation;
        use rand::distributions::Uniform;
        use rand::prelude::Distribution;
        let n_max = 10;
        let between = Uniform::<usize>::from(2..n_max);
        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let n = between.sample(&mut rng);
            let p1 = rand_perm(n, n * n / 4);
            let cycle_prod = perm_decompose(&p1);
            let obs_p1 = cycle_prod
                .iter()
                .fold(Permutation::identity(n), |acc, (p, q)| {
                    Permutation::transposition(n, *p, *q) * acc
                });
            assert_eq!(p1, obs_p1);
        }
    }

    #[test]
    fn in_place_permuting() {
        use crate::utils::{in_place_permute, rand_perm};
        use rand::distributions::Uniform;
        use rand::prelude::Distribution;
        let n_max = 10;
        let between = Uniform::<usize>::from(2..n_max);
        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let n = between.sample(&mut rng);
            let mut set = (0..n).map(|i| format!("{}", i)).collect::<Vec<String>>();
            let p1 = rand_perm(n, n * n / 4);
            in_place_permute(&mut set, &p1);
            for (idx, cur) in set.iter().enumerate() {
                assert_eq!(*cur, format!("{}", p1.apply(idx)));
            }
            in_place_permute(&mut set, &p1.inv());
            for (idx, cur) in set.iter().enumerate() {
                assert_eq!(*cur, format!("{}", idx));
            }
        }
    }
}
