use either::Either::{self, Left, Right};
use std::cmp::{max, min};
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
        self.middle.iter().map(|tup| tup.0).collect()
    }

    pub fn middle_to_right(&self) -> Vec<RightIndex> {
        self.middle.iter().map(|tup| tup.1).collect()
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
    pub fn map<F, Mu>(&self, f: F) -> Span<Mu>
    where
        F: Fn(Lambda) -> Mu,
        Mu: Sized + Eq + Copy + Debug,
    {
        Span::new(
            self.left.iter().map(|l| f(*l)).collect(),
            self.right.iter().map(|l| f(*l)).collect(),
            self.middle.clone(),
        )
    }

    pub fn is_jointly_injective(&self) -> bool {
        let mut seen = HashSet::with_capacity(self.middle.len());
        for cur_mid in &self.middle {
            if !seen.insert(*cur_mid) {
                return false;
            }
        }
        true
    }

    pub fn dagger(&self) -> Self {
        Self::new(
            self.codomain(),
            self.domain(),
            self.middle.iter().map(|(z, w)| (*w, *z)).collect(),
        )
    }
}

impl<Lambda> HasIdentity<Vec<Lambda>> for Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn identity(on_this: &Vec<Lambda>) -> Self {
        Self {
            middle: (0..on_this.len()).map(|idx| (idx, idx)).collect(),
            left: on_this.clone(),
            right: on_this.clone(),
            is_left_id: true,
            is_right_id: true,
        }
    }
}

pub fn dim_check<Lambda: Eq + Debug>(l: &[Lambda], r: &[Lambda]) -> Result<(), String> {
    if l.len() != r.len() {
        return Err("Mismatch in cardinalities of common interface".to_string());
    }
    let Some((w1,w2)) = l.iter().zip(r.iter()).find(|(a, b)| a != b) else { return Ok(())};
    return Err(format!(
        "Mismatch in labels of common interface. At some index there was {:?} vs {:?}",
        w1, w2
    ));
}

impl<Lambda> Composable<Vec<Lambda>> for Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn composable(&self, other: &Self) -> Result<(), String> {
        dim_check(&self.right, &other.left)
    }

    fn compose(&self, other: &Self) -> Result<Self, String> {
        self.composable(other)?;
        // could shortuct if self.is_right_id or other.is_left_id, but unnecessary
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

#[repr(transparent)]
pub struct Rel<Lambda: Eq + Sized + Debug + Copy>(Span<Lambda>);

impl<Lambda> HasIdentity<Vec<Lambda>> for Rel<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn identity(on_this: &Vec<Lambda>) -> Self {
        Self(Span::<Lambda>::identity(on_this))
    }
}

impl<Lambda> Composable<Vec<Lambda>> for Rel<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn compose(&self, other: &Self) -> Result<Self, String> {
        self.0.compose(&other.0).map(|x| Self(x))
    }

    fn domain(&self) -> Vec<Lambda> {
        self.0.domain()
    }

    fn codomain(&self) -> Vec<Lambda> {
        self.0.codomain()
    }

    fn composable(&self, other: &Self) -> Result<(), String> {
        self.0.composable(&other.0)
    }
}

impl<Lambda> Monoidal for Rel<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn monoidal(&mut self, other: Self) {
        self.0.monoidal(other.0);
    }
}

impl<Lambda> MonoidalMorphism<Vec<Lambda>> for Rel<Lambda> where Lambda: Sized + Eq + Copy + Debug {}

impl<Lambda> GenericMonoidalInterpretable<Lambda> for Rel<Lambda> where Lambda: Eq + Copy + Debug {}

impl<Lambda: Eq + Sized + Debug + Copy> Rel<Lambda> {
    fn new(x: Span<Lambda>, do_check: bool) -> Rel<Lambda> {
        if do_check {
            assert!(x.is_jointly_injective());
        }
        Rel::<Lambda>(x)
    }

    fn subsumes(&self, other: &Rel<Lambda>) -> bool {
        assert_eq!(self.domain(), other.domain());
        assert_eq!(self.codomain(), other.codomain());

        let self_pairs: HashSet<(usize, usize)> = HashSet::from_iter(self.0.middle.iter().cloned());
        let other_pairs: HashSet<(usize, usize)> =
            HashSet::from_iter(other.0.middle.iter().cloned());

        self_pairs.is_superset(&other_pairs)
    }

    #[allow(dead_code)]
    fn union(&self, other: &Self) -> Self {
        assert_eq!(self.domain(), other.domain());
        assert_eq!(self.codomain(), other.codomain());

        let mut ret_val = self.0.clone();
        for (x, y) in &other.0.middle {
            ret_val.add_middle((*x, *y)).unwrap();
        }
        Self(ret_val)
    }

    #[allow(dead_code)]
    fn intersection(&self, other: &Self) -> Self {
        assert_eq!(self.domain(), other.domain());
        assert_eq!(self.codomain(), other.codomain());

        let capacity = min(self.0.middle.len(), other.0.middle.len());
        let mut ret_val =
            Span::<Lambda>::new(self.domain(), self.codomain(), Vec::with_capacity(capacity));

        let self_pairs: HashSet<(usize, usize)> = HashSet::from_iter(self.0.middle.iter().cloned());
        let other_pairs: HashSet<(usize, usize)> =
            HashSet::from_iter(other.0.middle.iter().cloned());

        let in_common = self_pairs.intersection(&other_pairs);
        for (x, y) in in_common {
            ret_val.add_middle((*x, *y)).unwrap();
        }
        Self(ret_val)
    }

    #[allow(dead_code)]
    fn complement(&self) -> Result<Self, String> {
        let source_size = self.domain().len();
        let target_size = self.codomain().len();

        let capacity = source_size * target_size - self.0.middle.len();
        let mut ret_val =
            Span::<Lambda>::new(self.domain(), self.codomain(), Vec::with_capacity(capacity));

        let self_pairs: HashSet<(usize, usize)> = HashSet::from_iter(self.0.middle.iter().cloned());

        for (x, y) in (0..source_size).zip(0..target_size) {
            if !self_pairs.contains(&(x, y)) {
                ret_val.add_middle((x, y))?;
            }
        }
        Ok(Self(ret_val))
    }

    fn is_homogeneous(&self) -> bool {
        self.0.domain() == self.0.codomain()
    }

    fn is_reflexive(&self) -> bool {
        let identity_rel = Self::new(Span::<Lambda>::identity(&self.0.domain()), false);
        self.subsumes(&identity_rel)
    }

    #[allow(dead_code)]
    fn is_irreflexive(&self) -> bool {
        self.complement().map(|x| x.is_reflexive()).unwrap_or(false)
    }

    fn is_symmetric(&self) -> bool {
        let dagger = Self::new(self.0.dagger(), false);
        self.subsumes(&dagger)
    }

    #[allow(dead_code)]
    fn is_antisymmetric(&self) -> bool {
        let dagger = Self::new(self.0.dagger(), false);
        let intersect = self.intersection(&dagger);
        let identity_rel = Self::new(Span::<Lambda>::identity(&self.0.domain()), false);
        identity_rel.subsumes(&intersect)
    }

    fn is_transitive(&self) -> bool {
        let twice = Self::new(self.0.compose(&self.0).unwrap(), true);
        self.subsumes(&twice)
    }

    #[allow(dead_code)]
    fn is_equivalence_rel(&self) -> bool {
        if !self.is_homogeneous() {
            return false;
        }
        if !self.is_reflexive() {
            return false;
        }
        if !self.is_symmetric() {
            return false;
        }
        self.is_transitive()
    }

    #[allow(dead_code)]
    fn is_partial_order(&self) -> bool {
        if !self.is_homogeneous() {
            return false;
        }
        if !self.is_reflexive() {
            return false;
        }
        if !self.is_antisymmetric() {
            return false;
        }
        self.is_transitive()
    }
}
