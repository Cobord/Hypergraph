use std::fmt::Debug;

use crate::category::{Composable, HasIdentity};
use crate::monoidal::{Monoidal, MonoidalMorphism};
use crate::symmetric_monoidal::SymmetricMonoidalMorphism;

type LeftIndex = usize;
type RightIndex = usize;
#[allow(dead_code)]
type MiddleIndex = usize;

#[derive(Clone)]
#[allow(dead_code)]
pub struct Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    middle: Vec<(LeftIndex, RightIndex)>,
    left: Vec<Lambda>,
    right: Vec<Lambda>,
    is_left_id: bool,
    is_right_id: bool,
}

impl<Lambda> Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    #[allow(dead_code)]
    fn is_jointly_injective(&self) -> bool {
        todo!()
    }
}

impl<Lambda> HasIdentity<Vec<Lambda>> for Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn identity(_on_this: &Vec<Lambda>) -> Self {
        todo!()
    }
}

impl<Lambda> Composable<Vec<Lambda>> for Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn composable(&self, _other: &Self) -> Result<(), String> {
        todo!()
    }

    fn compose(&self, _other: &Self) -> Result<Self, String> {
        todo!()
    }

    fn domain(&self) -> Vec<Lambda> {
        todo!()
    }

    fn codomain(&self) -> Vec<Lambda> {
        todo!()
    }
}

impl<Lambda> Monoidal for Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn monoidal(&mut self, _other: Self) {
        todo!()
    }
}

impl<Lambda> MonoidalMorphism<Vec<Lambda>> for Span<Lambda> where Lambda: Sized + Eq + Copy + Debug {}

impl<Lambda> SymmetricMonoidalMorphism<Lambda> for Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn permute_side(&mut self, _p: &permutations::Permutation, _of_codomain: bool) {
        todo!()
    }

    fn from_permutation(
        _p: permutations::Permutation,
        _types: &[Lambda],
        _types_as_on_domain: bool,
    ) -> Self {
        todo!()
    }
}
