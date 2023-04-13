use either::Either::{self, Left, Right};
use std::cmp::max;
use std::collections::HashSet;
use std::fmt::Debug;

use crate::category::{Composable, HasIdentity};
use crate::monoidal::{GenericMonoidalInterpretable, Monoidal, MonoidalMorphism};
use crate::symmetric_monoidal::SymmetricMonoidalMorphism;
use crate::utils::{in_place_permute, represents_id};

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
    pub fn assert_valid(&self, check_id: bool) {
        let left_size = self.left.len();
        let left_in_bounds = self.middle.iter().all(|(z, _)| *z < left_size);
        assert!(
            left_in_bounds,
            "A target for one of the left arrows was out of bounds"
        );
        let right_size = self.right.len();
        let right_in_bounds = self.middle.iter().all(|(_, z)| *z < right_size);
        assert!(
            right_in_bounds,
            "A target for one of the right arrows was out of bounds"
        );
        let left_right_types_match = self
            .middle
            .iter()
            .all(|(z1, z2)| self.left[*z1] == self.right[*z2]);
        assert!(
            left_right_types_match,
            "There was a left and right linked by something in the span, but their lambda types didn't match"
        );
        if check_id {
            let is_left_really_id = represents_id(&self.middle_to_left());
            assert_eq!(
                is_left_really_id, self.is_left_id,
                "The identity nature of the left arrow was wrong"
            );
            let is_right_really_id = represents_id(&self.middle_to_right());
            assert_eq!(
                is_right_really_id, self.is_right_id,
                "The identity nature of the right arrow was wrong"
            );
        }
    }

    #[allow(dead_code)]
    pub fn new(
        left: Vec<Lambda>,
        right: Vec<Lambda>,
        middle: Vec<(LeftIndex, RightIndex)>,
    ) -> Self {
        let is_left_id = represents_id(&middle.iter().map(|tup| tup.0).collect::<Vec<LeftIndex>>());
        let is_right_id =
            represents_id(&middle.iter().map(|tup| tup.1).collect::<Vec<RightIndex>>());
        let answer = Self {
            middle,
            left,
            right,
            is_left_id,
            is_right_id,
        };
        answer.assert_valid(false);
        answer
    }

    pub fn middle_to_left(&self) -> Vec<LeftIndex> {
        self.middle
            .iter()
            .map(|tup| tup.0)
            .collect::<Vec<LeftIndex>>()
    }

    pub fn middle_to_right(&self) -> Vec<RightIndex> {
        self.middle
            .iter()
            .map(|tup| tup.1)
            .collect::<Vec<RightIndex>>()
    }

    #[allow(dead_code)]
    pub fn add_boundary_node(
        &mut self,
        new_boundary: Either<Lambda, Lambda>,
    ) -> Either<LeftIndex, RightIndex> {
        match new_boundary {
            Left(z) => {
                self.left.push(z);
                Left(self.left.len() - 1)
            }
            Right(z) => {
                self.right.push(z);
                Right(self.right.len() - 1)
            }
        }
    }

    pub fn add_middle(
        &mut self,
        new_middle: (LeftIndex, RightIndex),
    ) -> Result<MiddleIndex, String> {
        let type_left = self.left[new_middle.0];
        let type_right = self.right[new_middle.1];
        if type_left != type_right {
            return Err(format!(
                "Mismatched lambda values {:?} and {:?}",
                type_left, type_right
            ));
        }
        self.middle.push(new_middle);
        self.is_left_id = false;
        self.is_right_id = false;
        Ok(self.middle.len() - 1)
    }

    #[allow(dead_code)]
    pub fn change_lambda<F, Mu>(&self, f: F) -> Span<Mu>
    where
        F: Fn(Lambda) -> Mu,
        Mu: Sized + Eq + Copy + Debug,
    {
        Span::<Mu>::new(
            self.left.iter().map(|l| f(*l)).collect(),
            self.right.iter().map(|l| f(*l)).collect(),
            self.middle.clone(),
        )
    }

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
    fn composable(&self, other: &Self) -> Result<(), String> {
        let mut self_interface = self.right.iter();
        let mut other_interface = other.left.iter();
        let mut to_continue = true;
        while to_continue {
            let current_self = self_interface.next();
            let current_other = other_interface.next();
            match (current_self, current_other) {
                (None, None) => {
                    to_continue = false;
                }
                (Some(_), None) => {
                    return Err("Mismatch in cardinalities of common interface".to_string());
                }
                (None, Some(_)) => {
                    return Err("Mismatch in cardinalities of common interface".to_string());
                }
                (Some(w1), Some(w2)) => {
                    if w1 != w2 {
                        return Err(format!(
                            "Mismatch in labels of common interface. At some index there was {:?} vs {:?}",
                            w1, w2
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    fn compose(&self, other: &Self) -> Result<Self, String> {
        let _ = self.composable(other)?;
        #[allow(clippy::if_same_then_else)]
        if self.is_right_id {
            // todo shortcut
        } else if other.is_left_id {
            // todo shortcut
        }
        let max_middle = max(self.middle.len(), other.middle.len());
        let mut answer = Self::new(
            self.left.clone(),
            other.right.clone(),
            Vec::with_capacity(max_middle),
        );
        for (sl, sr) in self.middle.iter() {
            for (ol, or) in other.middle.iter() {
                if sr == ol {
                    let mid_added = answer.add_middle((*sl, *or));
                    match mid_added {
                        Ok(_) => {}
                        Err(z) => {
                            return Err(format!("{}\nShould be unreachable if composability already said it was all okay.",z));
                        }
                    }
                }
            }
        }
        Ok(answer)
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
