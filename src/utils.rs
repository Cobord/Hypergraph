use either::Either::{self, Left, Right};
use permutations::Permutation;
use rand::distributions::Uniform;
use rand::prelude::Distribution;

pub fn bimap<T, U, V, W, F, G>(x: Either<T, U>, f1: F, f2: G) -> Either<V, W>
where
    F: Fn(T) -> V,
    G: Fn(U) -> W,
{
    match x {
        Left(t) => Left(f1(t)),
        Right(u) => Right(f2(u)),
    }
}

pub fn either_f<T, U, V, F, G>(x: Either<T, U>, f1: F, f2: G) -> V
where
    F: Fn(T) -> V,
    G: Fn(U) -> V,
{
    match x {
        Left(t) => f1(t),
        Right(u) => f2(u),
    }
}

pub fn represents_id(arr: &[usize]) -> bool {
    let mut is_arr_id = true;
    for (arr_idx, tgt_idx) in arr.iter().enumerate() {
        if arr_idx != *tgt_idx {
            is_arr_id = false;
            break;
        }
    }
    is_arr_id
}

pub fn to_vec_01<A>(me: Option<A>) -> Vec<A> {
    match me {
        None => vec![],
        Some(z) => vec![z],
    }
}

pub fn keep_left<T: Copy, U>(me: &Either<T, U>) -> Option<T> {
    match me {
        Left(z) => Some(*z),
        Right(_) => None,
    }
}

pub fn position_max<T: Ord>(slice: &[T]) -> Option<usize> {
    slice
        .iter()
        .enumerate()
        .max_by(|(_, value0), (_, value1)| value0.cmp(value1))
        .map(|(idx, _)| idx)
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
        let pos_in_side_2 = side_2.iter().position(|t| *t == *cur);
        match pos_in_side_2 {
            None => {
                return Err("No permutation can take side 1 to side 2 \
                because an item in side 1 was not in side 2"
                    .to_string());
            }
            Some(idx) => {
                trial_perm.push(idx);
            }
        }
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
    let mut answer: Vec<(usize, usize)> = Vec::with_capacity(p.len() - 1);
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
        use rand::distributions::Uniform;
        use rand::prelude::Distribution;
        let n_max = 10;
        let between = Uniform::<usize>::from(2..n_max);
        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let my_n = between.sample(&mut rng);
            let my_set = (0..my_n).map(|i| format!("{}", i)).collect::<Vec<String>>();
            let p1 = rand_perm(my_n, my_n * my_n / 4);
            let permuted_set = p1.permute(&my_set);
            let found_perm = necessary_permutation(&my_set, &permuted_set);
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
            let my_n = between.sample(&mut rng);
            let p1 = rand_perm(my_n, my_n * my_n / 4);
            let cycle_prod = perm_decompose(&p1);
            let obs_p1 = cycle_prod
                .iter()
                .fold(Permutation::identity(my_n), |acc, (p, q)| {
                    Permutation::transposition(my_n, *p, *q) * acc
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
            let my_n = between.sample(&mut rng);
            let mut my_set = (0..my_n).map(|i| format!("{}", i)).collect::<Vec<String>>();
            let p1 = rand_perm(my_n, my_n * my_n / 4);
            in_place_permute(&mut my_set, &p1);
            for (idx, cur) in my_set.iter().enumerate() {
                assert_eq!(*cur, format!("{}", p1.apply(idx)));
            }
            in_place_permute(&mut my_set, &p1.inv());
            for (idx, cur) in my_set.iter().enumerate() {
                assert_eq!(*cur, format!("{}", idx));
            }
        }
    }
}
