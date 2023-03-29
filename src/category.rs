pub trait HasIdentity<T>: Sized {
    fn identity(on_this: &T) -> Self;
}

pub trait Composable<T: Eq>: Sized {
    fn compose(&self, other: &Self) -> Result<Self, String>;
    fn domain(&self) -> T;
    fn codomain(&self) -> T;
    fn composable(&self, other: &Self) -> Result<(), String> {
        if self.codomain() == other.domain() {
            Ok(())
        } else {
            Err("Not composable. No details on how domain and codomain mismatched".to_string())
        }
    }
}

pub trait ComposableMutating<T: Eq>: Sized {
    fn compose(&mut self, other: Self) -> Result<(), String>;
    fn domain(&self) -> T;
    fn codomain(&self) -> T;
    fn composable(&self, other: &Self) -> Result<(), String> {
        if self.codomain() == other.domain() {
            Ok(())
        } else {
            Err("Not composable. No details on how domain and codomain mismatched".to_string())
        }
    }
}
