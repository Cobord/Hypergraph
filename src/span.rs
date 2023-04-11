use std::collections::HashSet;
use std::fmt::Debug;

use crate::category::{Composable, HasIdentity};
use crate::monoidal::{GenericMonoidalInterpretable, Monoidal, MonoidalMorphism};
use crate::symmetric_monoidal::SymmetricMonoidalMorphism;
use crate::utils::in_place_permute;

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
        let mut seen = HashSet::with_capacity(self.middle.len());
        for cur_mid in &self.middle {
            if !seen.insert(*cur_mid) {
                return false;
            }
        }
        true
        //todo test
    }
}

impl<Lambda> HasIdentity<Vec<Lambda>> for Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn identity(on_this: &Vec<Lambda>) -> Self {
        Self {
            middle: (0..on_this.len()).map(|idx| (idx, idx)).collect::<Vec<_>>(),
            left: on_this.clone(),
            right: on_this.clone(),
            is_left_id: true,
            is_right_id: true,
        }
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
        self.left.clone()
    }

    fn codomain(&self) -> Vec<Lambda> {
        self.right.clone()
    }
}

impl<Lambda> Monoidal for Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn monoidal(&mut self, mut other: Self) {
        self.is_left_id &= other.is_left_id;
        self.is_right_id &= other.is_right_id;
        let left_shift = self.left.len();
        let right_shift = self.right.len();
        other.middle.iter_mut().for_each(|(v1, v2)| {
            *v1 += left_shift;
            *v2 += right_shift;
        });
        self.middle.extend(other.middle);
        self.left.extend(other.left);
        self.right.extend(other.right);
    }
}

impl<Lambda> MonoidalMorphism<Vec<Lambda>> for Span<Lambda> where Lambda: Sized + Eq + Copy + Debug {}

impl<Lambda> GenericMonoidalInterpretable<Lambda> for Span<Lambda> where Lambda: Eq + Copy + Debug {}

impl<Lambda> SymmetricMonoidalMorphism<Lambda> for Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn permute_side(&mut self, p: &permutations::Permutation, of_codomain: bool) {
        if of_codomain {
            self.is_right_id = false;
            in_place_permute(&mut self.right, p);
            self.middle.iter_mut().for_each(|(_, v2)| {
                *v2 = p.apply(*v2);
            });
        } else {
            self.is_left_id = false;
            in_place_permute(&mut self.left, p);
            self.middle.iter_mut().for_each(|(v1, _)| {
                *v1 = p.apply(*v1);
            });
        }
        //todo test
    }

    fn from_permutation(
        p: permutations::Permutation,
        types: &[Lambda],
        types_as_on_domain: bool,
    ) -> Self {
        if types_as_on_domain {
            let _answer = Self {
                left: types.to_vec(),
                middle: (0..types.len())
                    .map(|idx| (idx, p.apply(idx)))
                    .collect::<Vec<_>>(),
                right: p.permute(types),
                is_left_id: true,
                is_right_id: false,
            };
            todo!("p and p inverse straighten out")
        } else {
            let _answer = Self {
                left: p.permute(types),
                middle: (0..types.len())
                    .map(|idx| (p.apply(idx), idx))
                    .collect::<Vec<_>>(),
                right: types.to_vec(),
                is_left_id: false,
                is_right_id: true,
            };
            todo!("p and p inverse straighten out")
        }
    }
}
