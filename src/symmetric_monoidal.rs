use permutations::Permutation;

pub trait SymmetricMonoidalMorphism<T: Eq> {
    /*
    can pre/post compose a given morphism with a permutation (possibly panic if the permutation is not of the right cardinality)
    give the morphism : types[0] otimes \cdots -> types[p[0]] \otimes \cdots
        or the inverse (depending on types_as_on_domain)
        again can panic if the cardinality of the permutation does not match the cardinality of types
    */
    fn permute_side(&mut self, p: &Permutation, of_codomain: bool);
    fn from_permutation(p: Permutation, types: &[T], types_as_on_domain: bool) -> Self;
}

pub trait SymmetricMonoidalDiscreteMorphism<T: Eq> {
    /*
    for finset they are morphisms on finite sets, but rather than specify the domain/codomain as Vec<Singleton>
    the domain and codomain are just treated as usize, so we can't use the above trait where types was a slice
    */
    fn permute_side(&mut self, p: &Permutation, of_codomain: bool);
    fn from_permutation(p: Permutation, types: T, types_as_on_domain: bool) -> Self;
}
