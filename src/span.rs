use crate::category::CompositionError;

use {
    crate::{
        category::{Composable, HasIdentity},
        monoidal::{Monoidal, MonoidalMorphism},
        symmetric_monoidal::SymmetricMonoidalMorphism,
        utils::{in_place_permute, represents_id},
    },
    either::Either::{self, Left, Right},
    std::{collections::HashSet, fmt::Debug},
};

type LeftIndex = usize;
type RightIndex = usize;
type MiddleIndex = usize;

#[derive(Clone)]
pub struct Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    middle: Vec<(LeftIndex, RightIndex)>, // the leg maps from the source to the domain and codomain sets
    left: Vec<Lambda>,                    // the labels on the domain
    right: Vec<Lambda>,                   // the labels on the codomain
    is_left_id: bool,
    is_right_id: bool,
}

impl<Lambda> Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    pub fn assert_valid(&self, check_id_strong: bool, check_id_weak: bool) {
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
        if check_id_strong || (check_id_weak && self.is_left_id) {
            let is_left_really_id = represents_id(self.middle_to_left().into_iter());
            assert_eq!(
                is_left_really_id, self.is_left_id,
                "The identity nature of the left arrow was wrong"
            );
        }
        if check_id_strong || (check_id_weak && self.is_right_id) {
            let is_right_really_id = represents_id(self.middle_to_right().into_iter());
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
        let is_left_id = represents_id(middle.iter().map(|tup| tup.0));
        let is_right_id = represents_id(middle.iter().map(|tup| tup.1));
        let answer = Self {
            middle,
            left,
            right,
            is_left_id,
            is_right_id,
        };
        answer.assert_valid(false, false);
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
        /*
        add a new boundary node with specified label
        which side depends on whether Left or Right
        it is not in the image of the leg maps
        but the index is returned so the caller
            can put it in the image of the leg maps later
        */
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
        /*
        add a new node at the source
        the leg maps on this new node send it to the specified indices
        the labels of these two targets must match up
        upon success, the index of this new node is returned
        */
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
        /*
        change the labels with the function f
        */
        Span::new(
            self.left.iter().map(|l| f(*l)).collect(),
            self.right.iter().map(|l| f(*l)).collect(),
            self.middle.clone(),
        )
    }

    pub fn is_jointly_injective(&self) -> bool {
        /*
        could this span be interpreted as a Relation instead of just a span
        if the leg maps are jointly injective, then might as well say the source node
        is a subset of the domain \times codomain, instead of it's own new set
        */
        crate::utils::is_unique(&self.middle)
    }

    pub fn dagger(&self) -> Self {
        /*
        flip the domain and codomain
        */
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

impl<Lambda> Composable<Vec<Lambda>> for Span<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
{
    fn composable(&self, other: &Self) -> Result<(), CompositionError> {
        crate::utils::same_labels_check(self.right.iter(), other.left.iter())
            .map_err(CompositionError::from)
    }

    fn compose(&self, other: &Self) -> Result<Self, CompositionError> {
        self.composable(other)?;
        // could shortuct if self.is_right_id or other.is_left_id, but unnecessary
        let max_middle = self.middle.len().max(other.middle.len());
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
                            return Err(format!("{}\nShould be unreachable if composability already said it was all okay.",z).into());
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
                middle: (0..types.len()).map(|idx| (idx, p.apply(idx))).collect(),
                right: p.permute(types),
                is_left_id: true,
                is_right_id: false,
            };
            todo!("p and p inverse straighten out")
        } else {
            let _answer = Self {
                left: p.permute(types),
                middle: (0..types.len()).map(|idx| (p.apply(idx), idx)).collect(),
                right: types.to_vec(),
                is_left_id: false,
                is_right_id: true,
            };
            todo!("p and p inverse straighten out")
        }
    }
}

/*
wrapper around span for rel
where the source is now always assumed to be a subset of the product
by the leg maps being jointly injective
*/
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
    fn compose(&self, other: &Self) -> Result<Self, CompositionError> {
        self.0.compose(&other.0).map(|x| Self(x))
    }

    fn domain(&self) -> Vec<Lambda> {
        self.0.domain()
    }

    fn codomain(&self) -> Vec<Lambda> {
        self.0.codomain()
    }

    fn composable(&self, other: &Self) -> Result<(), CompositionError> {
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

impl<Lambda: Eq + Sized + Debug + Copy> Rel<Lambda> {
    fn new(x: Span<Lambda>, do_check: bool) -> Self {
        /*
        given a span interpret it as a relation
        if not do_check, then assume that this is possible
        otherwise makes sure this is possible with the
        leg maps actually being jointly injective
        */
        if do_check {
            assert!(x.is_jointly_injective());
        }
        Self(x)
    }

    fn subsumes(&self, other: &Rel<Lambda>) -> bool {
        /*
        given two relations on the same domain and codomain (A and B)
        we have two subsets of A \times B
        is the one for self a superset of the one for other
        */
        assert_eq!(self.domain(), other.domain());
        assert_eq!(self.codomain(), other.codomain());

        let self_pairs: HashSet<(usize, usize)> = HashSet::from_iter(self.0.middle.iter().cloned());
        let other_pairs: HashSet<(usize, usize)> =
            HashSet::from_iter(other.0.middle.iter().cloned());

        self_pairs.is_superset(&other_pairs)
    }

    #[allow(dead_code)]
    fn union(&self, other: &Self) -> Self {
        /*
        given two relations on the same domain and codomain (A and B)
        we have two subsets of A \times B
        make a new relation with the union of those two
        */
        assert_eq!(self.domain(), other.domain());
        assert_eq!(self.codomain(), other.codomain());

        let self_pairs: HashSet<(usize, usize)> = HashSet::from_iter(self.0.middle.iter().cloned());
        let mut ret_val = self.0.clone();
        for (x, y) in &other.0.middle {
            if !self_pairs.contains(&(*x, *y)) {
                /*
                the reason this would panic is if the labels mismatched
                but because the labels for the Left(x) and Right(y) nodes
                matched when other was created, we know they do
                so the unwrap should never panic
                */
                ret_val.add_middle((*x, *y)).unwrap();
            }
        }
        Self(ret_val)
    }

    fn intersection(&self, other: &Self) -> Self {
        /*
        given two relations on the same domain and codomain (A and B)
        we have two subsets of A \times B
        make a new relation with the intesection of those two
        */
        assert_eq!(self.domain(), other.domain());
        assert_eq!(self.codomain(), other.codomain());

        let capacity = self.0.middle.len().min(other.0.middle.len());
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

    fn complement(&self) -> Result<Self, String> {
        /*
        say self is a relation with domain and codomain A and B
        make a new relation with (A \times B) \setminus self
        there can be errors if there are label mismatches
        */
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
        /*
        a relation with the same domain and codomain
        */
        self.0.domain() == self.0.codomain()
    }

    fn is_reflexive(&self) -> bool {
        /*
        a relation with the same domain and codomain A
        such that \forall x \in A : R(x,x)
        */
        let identity_rel = Self::new(Span::<Lambda>::identity(&self.0.domain()), false);
        self.subsumes(&identity_rel)
    }

    #[allow(dead_code)]
    fn is_irreflexive(&self) -> bool {
        /*
        is the complement reflexive
        if there are label mismatches when trying to create the complement, then return false
        */
        self.complement().map(|x| x.is_reflexive()).unwrap_or(false)
    }

    fn is_symmetric(&self) -> bool {
        /*
        a relation with the same domain and codomain A
        such that \forall x,y \in A : R(x,y) -> R(y,x)
        */
        let dagger = Self::new(self.0.dagger(), false);
        self.subsumes(&dagger)
    }

    fn is_antisymmetric(&self) -> bool {
        /*
        a relation with the same domain and codomain A
        such that \forall x \neq y \in A : \neg ( R(x,y) ^ R(y,x) )
        */
        let dagger = Self::new(self.0.dagger(), false);
        let intersect = self.intersection(&dagger);
        let identity_rel = Self::new(Span::<Lambda>::identity(&self.0.domain()), false);
        identity_rel.subsumes(&intersect)
    }

    fn is_transitive(&self) -> bool {
        /*
        self(x,y) ^ self(y,z) means that twice(x,z)
        is self(x,z) by itself true
        */
        let twice = Self::new(self.0.compose(&self.0).unwrap(), true);
        self.subsumes(&twice)
    }

    #[allow(dead_code)]
    fn is_equivalence_rel(&self) -> bool {
        /*
        is this an equivalence relation
        so we can interpret a pair (x,y) being in the source of this relation as x \equiv y
        and not equivalent otherwise
        */
        self.is_homogeneous() && self.is_reflexive() && self.is_symmetric() && self.is_transitive()
    }

    #[allow(dead_code)]
    fn is_partial_order(&self) -> bool {
        /*
        is this a partial order
        so we can interpret a pair (x,y) being in the source of this relation as x \leq y
        and not \leq otherwise
        */
        self.is_homogeneous()
            && self.is_reflexive()
            && self.is_antisymmetric()
            && self.is_transitive()
    }
}
