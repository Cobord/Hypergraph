pub trait HasIdentity<T>: Sized {
    fn identity(on_this: &T) -> Self;
}

#[allow(dead_code)]
#[derive(Debug)]
pub enum CompositionError {
    CompositionError(String),
}

impl From<String> for CompositionError {
    fn from(value: String) -> Self {
        Self::CompositionError(value)
    }
}

impl From<&str> for CompositionError {
    fn from(value: &str) -> Self {
        Self::CompositionError(value.to_string())
    }
}

pub trait Composable<T: Eq>: Sized {
    fn compose(&self, other: &Self) -> Result<Self, CompositionError>;
    fn domain(&self) -> T;
    fn codomain(&self) -> T;
    fn composable(&self, other: &Self) -> Result<(), CompositionError> {
        if self.codomain() == other.domain() {
            Ok(())
        } else {
            Err(
                "Not composable. No details on how domain and codomain mismatched"
                    .to_string()
                    .into(),
            )
        }
    }
}

pub trait ComposableMutating<T: Eq>: Sized {
    fn compose(&mut self, other: Self) -> Result<(), CompositionError>;
    fn domain(&self) -> T;
    fn codomain(&self) -> T;
    fn composable(&self, other: &Self) -> Result<(), CompositionError> {
        if self.codomain() == other.domain() {
            Ok(())
        } else {
            Err(
                "Not composable. No details on how domain and codomain mismatched"
                    .to_string()
                    .into(),
            )
        }
    }
}
