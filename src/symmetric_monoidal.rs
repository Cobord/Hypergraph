use permutations::Permutation;

use crate::monoidal::MonoidalMorphism;

pub trait SymmetricMonoidalMorphism<T>: MonoidalMorphism<T> {
    fn permute_side(&mut self, p: &Permutation, of_codomain: bool);
    fn from_permutation(p: Permutation, types: &T, types_as_on_domain: bool) -> Self;
}
