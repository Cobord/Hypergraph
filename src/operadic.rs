#[derive(PartialEq, Eq, Debug)]
pub enum OperadicError {
    OperadicError(String),
}

impl From<String> for OperadicError {
    fn from(value: String) -> Self {
        Self::OperadicError(value)
    }
}

impl From<&str> for OperadicError {
    fn from(value: &str) -> Self {
        Self::OperadicError(value.to_string())
    }
}

pub trait Operadic<InputLabel> {
    /*
    change the n-ary operation self to the one where
        the argument specified by which_input has been
        grafted with the m-ary operation other_obj
    This can fail for reasons as follows
        none of the n for self
            are labelled as which_input
        the types for
            - the output of other_obj
            - the which_input of self
        don't line up
    */
    #[allow(dead_code)]
    fn operadic_substitution(
        &mut self,
        which_input: InputLabel,
        other_obj: Self,
    ) -> Result<(), OperadicError>;
}
