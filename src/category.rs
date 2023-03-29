pub trait HasIdentity<T>: Sized {
    fn identity(on_this: &T) -> Self;
}

pub trait Composable<T>: Sized {
    fn compose(&self, other: &Self) -> Result<Self, String>;
    fn domain(&self) -> T;
    fn codomain(&self) -> T;
}

pub trait ComposableMutating<T>: Sized {
    fn compose(&mut self, other: Self) -> Result<(), String>;
    fn domain(&self) -> T;
    fn codomain(&self) -> T;
}
