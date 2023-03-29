use crate::category::{Composable, ComposableMutating};

pub trait Monoidal {
    fn monoidal(&mut self, other: Self);
}

pub trait MonoidalMorphism<T>: Monoidal + Composable<T> {}
pub trait MonoidalMutatingMorphism<T>: Monoidal + ComposableMutating<T> {}
