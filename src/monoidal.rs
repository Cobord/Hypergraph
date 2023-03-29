use crate::category::{Composable, ComposableMutating};

pub trait Monoidal {
    fn monoidal(&mut self, other: Self);
}

pub trait MonoidalMorphism<T: Eq>: Monoidal + Composable<T> {}
pub trait MonoidalMutatingMorphism<T: Eq>: Monoidal + ComposableMutating<T> {}
