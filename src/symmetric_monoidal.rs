use {
    crate::monoidal::{MonoidalMorphism, MonoidalMutatingMorphism},
    permutations::Permutation,
};

pub trait SymmetricMonoidalMorphism<T: Eq>: MonoidalMorphism<Vec<T>> {
    fn permute_side(&mut self, p: &Permutation, of_codomain: bool);
    fn from_permutation(p: Permutation, types: &[T], types_as_on_domain: bool) -> Self;
}

pub trait SymmetricMonoidalDiscreteMorphism<T: Eq>: MonoidalMorphism<T> {
    fn permute_side(&mut self, p: &Permutation, of_codomain: bool);
    fn from_permutation(p: Permutation, types: T, types_as_on_domain: bool) -> Self;
}

pub trait SymmetricMonoidalMutatingMorphism<T: Eq>: MonoidalMutatingMorphism<Vec<T>> {
    fn permute_side(&mut self, p: &Permutation, of_codomain: bool);
    fn from_permutation(p: Permutation, types: &[T], types_as_on_domain: bool) -> Self;
}
