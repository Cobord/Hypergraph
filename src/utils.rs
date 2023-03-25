use either::Either::{self, Left, Right};

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
