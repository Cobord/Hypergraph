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
    fn operadic_substitution(
        &mut self,
        which_input: InputLabel,
        other_obj: Self,
    ) -> Result<(), String>;
}
