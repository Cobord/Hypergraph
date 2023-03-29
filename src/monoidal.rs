use crate::category::Composable;

pub trait Monoidal {
    fn monoidal(&mut self, other: Self);
}

pub trait MonoidalMorphism<T>: Monoidal + Composable<T> {}
