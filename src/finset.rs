use crate::category::CompositionError;

use {
    crate::{
        category::{Composable, HasIdentity},
        monoidal::{Monoidal, MonoidalMorphism},
        symmetric_monoidal::SymmetricMonoidalDiscreteMorphism,
    },
    permutations::Permutation,
    std::{collections::HashSet, error, fmt},
};

pub type FinSetMap = Vec<usize>;
pub type FinSetMorphism = (Vec<usize>, usize);

impl HasIdentity<usize> for FinSetMorphism {
    fn identity(on_this: &usize) -> Self {
        ((0..*on_this).collect(), 0)
    }
}

impl Monoidal for FinSetMorphism {
    fn monoidal(&mut self, other: Self) {
        let other_empty = other.0.is_empty();
        let self_codomain = self.codomain();
        self.0.extend(other.0.iter().map(|o| o + self_codomain));
        if other_empty {
            self.1 += other.1;
        } else {
            self.1 = other.1;
        }
    }
}

impl Composable<usize> for FinSetMorphism {
    fn compose(&self, other: &Self) -> Result<Self, CompositionError> {
        if self.composable(other).is_err() {
            return Err(format!(
                "Not composable. The codomain of self was {}. The domain of other was {}",
                self.codomain(),
                other.domain()
            )
            .into());
        }
        let other_codomain = other.codomain();
        let composite: Vec<_> = (0..self.domain()).map(|s| other.0[self.0[s]]).collect();
        let ret = if let Some(max_val) = composite.iter().max() {
            (other_codomain - max_val - 1).max(0)
        } else {
            other_codomain
        };
        Ok((composite, ret))
    }

    fn domain(&self) -> usize {
        self.0.len()
    }

    fn codomain(&self) -> usize {
        self.1
            + if let Some(max_val) = self.0.iter().max() {
                max_val + 1
            } else {
                0
            }
    }
}

impl MonoidalMorphism<usize> for FinSetMorphism {}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct OrderPresSurj {
    preimage_card_minus_1: Vec<usize>,
}

impl<const N: usize> From<[usize; N]> for OrderPresSurj {
    fn from(value: [usize; N]) -> Self {
        Self {
            preimage_card_minus_1: value.to_vec(),
        }
    }
}

impl HasIdentity<usize> for OrderPresSurj {
    fn identity(on_this: &usize) -> Self {
        Self {
            preimage_card_minus_1: vec![0; *on_this],
        }
    }
}

impl Monoidal for OrderPresSurj {
    fn monoidal(&mut self, other: Self) {
        self.preimage_card_minus_1
            .extend(other.preimage_card_minus_1);
    }
}

impl Composable<usize> for OrderPresSurj {
    fn compose(&self, other: &Self) -> Result<Self, CompositionError> {
        if self.composable(other).is_err() {
            return Err(format!(
                "Not composable. The codomain of self was {}. The domain of other was {}",
                self.codomain(),
                other.domain()
            )
            .into());
        }
        let codomain = other.codomain();
        let mut answer = Vec::with_capacity(codomain);
        let mut self_idx = 0;
        for idx in 0..codomain {
            let how_many_mid = other.preimage_card_minus_1[idx] + 1;
            let preimage_card_cur: usize = self.preimage_card_minus_1
                [self_idx..self_idx + how_many_mid]
                .iter()
                .sum::<usize>()
                + how_many_mid;
            answer.push(preimage_card_cur - 1);
            self_idx += how_many_mid;
        }
        Ok(Self {
            preimage_card_minus_1: answer,
        })
    }

    fn domain(&self) -> usize {
        self.preimage_card_minus_1.iter().sum::<usize>() + self.preimage_card_minus_1.len()
    }

    fn codomain(&self) -> usize {
        self.preimage_card_minus_1.len()
    }
}

impl MonoidalMorphism<usize> for OrderPresSurj {}

impl OrderPresSurj {
    fn to_ordinary(&self) -> FinSetMorphism {
        let domain_size: usize = self.domain();
        let mut answer = Vec::with_capacity(domain_size);
        for (cur_target, v) in self.preimage_card_minus_1.iter().enumerate() {
            answer.extend(std::iter::repeat_n(cur_target, v + 1));
        }

        (answer, 0)
    }

    fn apply(&self, test_pt: usize) -> usize {
        self.to_ordinary().0[test_pt]
    }

    pub fn preimage_cardinalities(&self) -> Vec<usize> {
        self.preimage_card_minus_1.iter().map(|z| z + 1).collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderPresInj {
    counts_iden_unit_alternating: Vec<usize>,
}

impl HasIdentity<usize> for OrderPresInj {
    fn identity(on_this: &usize) -> Self {
        Self {
            counts_iden_unit_alternating: vec![*on_this],
        }
    }
}

impl Monoidal for OrderPresInj {
    fn monoidal(&mut self, other: Self) {
        if self.counts_iden_unit_alternating.len() % 2 == 1 {
            self.counts_iden_unit_alternating.push(0);
        }
        self.counts_iden_unit_alternating
            .extend(other.counts_iden_unit_alternating);
    }
}

impl Composable<usize> for OrderPresInj {
    fn compose(&self, other: &Self) -> Result<Self, CompositionError> {
        if self.composable(other).is_err() {
            return Err(format!(
                "Not composable. The codomain of self was {}. The domain of other was {}",
                self.codomain(),
                other.domain()
            )
            .into());
        }
        let ord_self = self.to_ordinary();
        let ord_other = other.to_ordinary();
        let composite = ord_self.compose(&ord_other)?;
        Self::try_from(composite).map_err(|_| "???".into())
    }

    fn domain(&self) -> usize {
        self.counts_iden_unit_alternating
            .iter()
            .enumerate()
            .map(|(n, v)| ((n + 1) % 2) * v)
            .sum::<usize>()
    }

    fn codomain(&self) -> usize {
        let mut cur_target = 0;
        for (n, v) in self.counts_iden_unit_alternating.iter().enumerate() {
            if n % 2 == 0 {
                for _ in 0..*v {
                    cur_target += 1;
                }
            } else {
                cur_target += v;
            }
        }
        cur_target
    }
}

impl MonoidalMorphism<usize> for OrderPresInj {}

impl OrderPresInj {
    fn to_ordinary(&self) -> FinSetMorphism {
        let domain_size: usize = self.domain();
        let mut answer = Vec::with_capacity(domain_size);
        let mut cur_target = 0;
        let mut codomain_minus_greatest_range = 0;
        for (n, v) in self.counts_iden_unit_alternating.iter().enumerate() {
            if n % 2 == 0 {
                codomain_minus_greatest_range = 0;
                for _ in 0..*v {
                    answer.push(cur_target);
                    cur_target += 1;
                }
            } else {
                codomain_minus_greatest_range = *v;
                cur_target += v;
            }
        }
        (answer, codomain_minus_greatest_range)
    }

    fn apply(&self, test_pt: usize) -> usize {
        self.to_ordinary().0[test_pt]
    }

    pub fn iden_unit_counts(&self) -> Vec<usize> {
        self.counts_iden_unit_alternating.clone()
    }
}

fn is_surjective(v: &[usize]) -> bool {
    // empty set to empty set
    let Some(max_val) = v.iter().max() else {
        return true;
    };
    if v.len() < max_val + 1 {
        return false;
    }

    let seen: HashSet<_> = v.iter().collect();
    seen.len() == max_val + 1
}

fn is_injective(v: &[usize]) -> bool {
    // empty set to empty set
    let Some(max_val) = v.iter().max() else {
        return true;
    };
    if v.len() > max_val + 1 {
        return false;
    }
    crate::utils::is_unique(v)
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TryFromSurjError;
impl fmt::Display for TryFromSurjError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ill-formed slice to order preserving surjection conversion attempted"
        )
    }
}

impl TryFrom<FinSetMorphism> for OrderPresSurj {
    type Error = TryFromSurjError;
    fn try_from(v_mor: FinSetMorphism) -> Result<Self, Self::Error> {
        if v_mor.1 > 0 {
            return Err(TryFromSurjError);
        }
        let v = v_mor.0;
        if !v.iter().is_sorted() || !is_surjective(&v) {
            return Err(TryFromSurjError);
        }
        if v.is_empty() {
            return Ok(Self::default());
        }
        let mut cur_i = 0;
        let mut count_of_cur_i = 0;
        let max = *v.last().unwrap();
        let mut preimage_card_minus_1 = Vec::with_capacity(max);
        for cur_v in v {
            if cur_v > cur_i {
                preimage_card_minus_1.push(count_of_cur_i - 1);
                cur_i = cur_v;
                count_of_cur_i = 1;
            } else {
                count_of_cur_i += 1;
            }
        }
        preimage_card_minus_1.push(count_of_cur_i - 1);
        preimage_card_minus_1.shrink_to_fit();
        Ok(Self {
            preimage_card_minus_1,
        })
    }
}
impl error::Error for TryFromSurjError {}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TryFromInjError;
impl fmt::Display for TryFromInjError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ill-formed slice to order preserving injection conversion attempted"
        )
    }
}

impl TryFrom<FinSetMorphism> for OrderPresInj {
    type Error = TryFromInjError;
    fn try_from(v_mor: FinSetMorphism) -> Result<Self, Self::Error> {
        let v = v_mor.0;
        if !v.iter().is_sorted() || !is_injective(&v) {
            return Err(TryFromInjError);
        }
        if v.is_empty() {
            return Ok(Self {
                counts_iden_unit_alternating: vec![],
            });
        }
        let mut previous_entry_plus_1 = 0;
        let mut cur_consecutive = 0;
        let mut counts_iden_unit_alternating = Vec::with_capacity(1 + v.len() * 2);
        for cur_v in v {
            if cur_v == previous_entry_plus_1 {
                cur_consecutive += 1;
            } else {
                counts_iden_unit_alternating.push(cur_consecutive);
                counts_iden_unit_alternating.push(cur_v - previous_entry_plus_1);
                cur_consecutive = 1;
            }
            previous_entry_plus_1 = cur_v + 1;
        }
        if cur_consecutive > 0 {
            counts_iden_unit_alternating.push(cur_consecutive);
            if v_mor.1 > 0 {
                counts_iden_unit_alternating.push(v_mor.1);
            }
        } else if v_mor.1 > 0 {
            counts_iden_unit_alternating.push(0);
            counts_iden_unit_alternating.push(v_mor.1);
        }
        counts_iden_unit_alternating.shrink_to_fit();
        Ok(Self {
            counts_iden_unit_alternating,
        })
    }
}
impl error::Error for TryFromInjError {}

fn permutation_sort<T: Ord>(x: &mut [T]) -> Permutation {
    let mut answer: FinSetMap = (0..x.len()).collect();
    answer.sort_by(|a, b| x[*a].cmp(&x[*b]));
    x.sort();
    Permutation::try_from(answer).unwrap()
}

#[allow(dead_code)]
pub fn from_cycle(n: usize, cycle: &[usize]) -> Permutation {
    if cycle.len() < 2 {
        return Permutation::identity(n);
    }
    let part1 = Permutation::transposition(n, cycle[0], cycle[1]);
    from_cycle(n, &cycle[1..]) * part1
}

pub struct Decomposition {
    permutation_part: Permutation,
    order_preserving_surjection: OrderPresSurj,
    order_preserving_injection: OrderPresInj,
}

impl HasIdentity<usize> for Decomposition {
    fn identity(on_this: &usize) -> Self {
        Self {
            permutation_part: Permutation::identity(*on_this),
            order_preserving_surjection: OrderPresSurj::identity(on_this),
            order_preserving_injection: OrderPresInj::identity(on_this),
        }
    }
}

impl Monoidal for Decomposition {
    fn monoidal(&mut self, other: Self) {
        let self_len = self.permutation_part.len();
        let other_permutation_shifted = (0..other.permutation_part.len())
            .map(|idx| other.permutation_part.apply(idx) + self_len);
        let mut perm_underlying = (0..self_len)
            .map(|idx| self.permutation_part.apply(idx))
            .collect::<Vec<usize>>();
        perm_underlying.extend(other_permutation_shifted);
        self.permutation_part = Permutation::try_from(perm_underlying).unwrap();
        self.order_preserving_surjection
            .monoidal(other.order_preserving_surjection);
        self.order_preserving_injection
            .monoidal(other.order_preserving_injection);
    }
}

impl Composable<usize> for Decomposition {
    fn compose(&self, other: &Self) -> Result<Self, CompositionError> {
        if self.composable(other).is_err() {
            return Err(format!(
                "Not composable. The codomain of self was {}. The domain of other was {}",
                self.codomain(),
                other.domain()
            )
            .into());
        }
        let other_codomain = other.codomain();
        let ord_self = self.to_ordinary();
        let ord_other = other.to_ordinary();
        let composite = ord_self.compose(&ord_other)?;
        if let Some(max_val) = composite.0.iter().max() {
            let leftover_needed = (other_codomain - max_val - 1).max(0);
            Self::try_from((composite.0, leftover_needed)).map_err(|_| "???".into())
        } else {
            Self::try_from(composite).map_err(|_| "???".into())
        }
    }

    fn domain(&self) -> usize {
        self.permutation_part.len()
    }

    fn codomain(&self) -> usize {
        self.order_preserving_injection.codomain()
    }
}

impl MonoidalMorphism<usize> for Decomposition {}

impl SymmetricMonoidalDiscreteMorphism<usize> for Decomposition {
    fn permute_side(&mut self, p: &Permutation, of_codomain: bool) {
        #[allow(clippy::if_not_else)]
        if !of_codomain {
            assert_eq!(p.len(), self.domain());
            self.permutation_part = p * self.permutation_part.clone();
            todo!("might be p.inv() instead or the multiplication might be backwards")
        } else {
            assert_eq!(p.len(), self.codomain());
            let p_decompose = Self::from_permutation(p.clone(), p.len(), true);
            let new_self = self.compose(&p_decompose).unwrap();
            *self = new_self;
            todo!("might be p.inv() instead")
        }
    }

    fn from_permutation(p: Permutation, perm_len: usize, _: bool) -> Self {
        assert_eq!(p.len(), perm_len);
        Self {
            permutation_part: p,
            order_preserving_injection: OrderPresInj::identity(&perm_len),
            order_preserving_surjection: OrderPresSurj::identity(&perm_len),
        }
    }
}

impl Decomposition {
    fn apply(&self, test_pt: usize) -> usize {
        let dest_after_perm = self.permutation_part.apply(test_pt);
        let dest_after_surj = self.order_preserving_surjection.apply(dest_after_perm);
        self.order_preserving_injection.apply(dest_after_surj)
    }

    fn to_ordinary(&self) -> FinSetMorphism {
        let wanted_codomain = self.codomain();
        let map_part: FinSetMap = (0..self.domain()).map(|z| self.apply(z)).collect();
        if let Some(max_val) = map_part.iter().max() {
            let leftover_needed = (wanted_codomain - max_val - 1).max(0);
            (map_part, leftover_needed)
        } else {
            (map_part, wanted_codomain)
        }
    }

    pub const fn get_parts(&self) -> (&Permutation, &OrderPresSurj, &OrderPresInj) {
        (
            &self.permutation_part,
            &self.order_preserving_surjection,
            &self.order_preserving_injection,
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TryFromFinSetError;
impl fmt::Display for TryFromFinSetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ill-formed slice to order preserving map conversion attempted"
        )
    }
}

impl TryFrom<FinSetMorphism> for Decomposition {
    type Error = TryFromFinSetError;
    fn try_from(v_mor: FinSetMorphism) -> Result<Self, TryFromFinSetError> {
        let mut v = v_mor.0;
        let permutation_part = if v.iter().is_sorted() {
            Permutation::identity(v.len())
        } else {
            permutation_sort(&mut v).inv()
        };
        let (epic_part, monic_part) = monotone_epi_mono_fact(v);
        let order_preserving_surjection =
            OrderPresSurj::try_from((epic_part, 0)).map_err(|_| TryFromFinSetError)?;
        let order_preserving_injection =
            OrderPresInj::try_from((monic_part, v_mor.1)).map_err(|_| TryFromFinSetError)?;
        Ok(Self {
            permutation_part,
            order_preserving_surjection,
            order_preserving_injection,
        })
    }
}
impl error::Error for TryFromFinSetError {}

#[allow(clippy::needless_pass_by_value)]
fn monotone_epi_mono_fact(v: FinSetMap) -> (FinSetMap, FinSetMap) {
    if v.is_empty() {
        return (vec![], vec![]);
    }
    let mut surj_part = v.clone();
    let mut inj_part = Vec::with_capacity(v.len());
    let mut v_iter = v.iter();
    let mut cur_index = 0;
    let first = v_iter.next().unwrap();
    let mut current_image_number = 0;
    let mut current_image_number_in_tgt = first;
    surj_part[cur_index] = current_image_number;
    inj_part.push(*first);
    for cur_item in v_iter {
        cur_index += 1;
        if cur_item == current_image_number_in_tgt {
            surj_part[cur_index] = current_image_number;
        } else {
            current_image_number += 1;
            current_image_number_in_tgt = cur_item;
            surj_part[cur_index] = current_image_number;
            inj_part.push(*cur_item);
        }
    }
    inj_part.shrink_to_fit();
    (surj_part, inj_part)
}

mod test {

    #[test]
    fn surjectivity() {
        use crate::finset::{is_surjective, FinSetMap};
        let mut cur_test: FinSetMap = vec![];
        assert!(is_surjective(&cur_test));
        cur_test = vec![0];
        assert!(is_surjective(&cur_test));
        cur_test = vec![1];
        assert!(!is_surjective(&cur_test));
        cur_test = vec![2];
        assert!(!is_surjective(&cur_test));
        cur_test = vec![12490];
        assert!(!is_surjective(&cur_test));
        cur_test = vec![0, 1, 2];
        assert!(is_surjective(&cur_test));
        cur_test = vec![0, 2, 1];
        assert!(is_surjective(&cur_test));
        cur_test = vec![2, 1];
        assert!(!is_surjective(&cur_test));
        cur_test = vec![0, 3, 1, 2];
        assert!(is_surjective(&cur_test));
        cur_test = vec![1, 1, 2];
        assert!(!is_surjective(&cur_test));
        cur_test = vec![0, 1, 1, 2];
        assert!(is_surjective(&cur_test));
    }

    #[test]
    fn injectivity() {
        use crate::finset::{is_injective, FinSetMap};
        let mut cur_test: FinSetMap = vec![];
        assert!(is_injective(&cur_test));
        cur_test = vec![0];
        assert!(is_injective(&cur_test));
        cur_test = vec![1];
        assert!(is_injective(&cur_test));
        cur_test = vec![2];
        assert!(is_injective(&cur_test));
        cur_test = vec![12490];
        assert!(is_injective(&cur_test));
        cur_test = vec![0, 1, 2];
        assert!(is_injective(&cur_test));
        cur_test = vec![0, 2, 1];
        assert!(is_injective(&cur_test));
        cur_test = vec![2, 1];
        assert!(is_injective(&cur_test));
        cur_test = vec![0, 3, 1, 2];
        assert!(is_injective(&cur_test));
        cur_test = vec![1, 1, 2];
        assert!(!is_injective(&cur_test));
        cur_test = vec![0, 1, 1, 2];
        assert!(!is_injective(&cur_test));
    }

    #[test]
    fn ord_surj_conversion() {
        use super::{FinSetMap, OrderPresSurj, TryFromSurjError};
        use crate::category::Composable;
        let mut cur_test: FinSetMap = vec![];
        let mut cur_result = Ok(OrderPresSurj::default());
        assert_eq!(cur_result, OrderPresSurj::try_from((cur_test, 0)));

        cur_test = vec![0];
        cur_result = Ok([0].into());
        assert_eq!(cur_result, OrderPresSurj::try_from((cur_test.clone(), 0)));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }
        assert_eq!(cur_result_unwrapped.domain(), 1);
        assert_eq!(cur_result_unwrapped.codomain(), 1);
        let cur_composed = cur_result_unwrapped
            .compose(&cur_result_unwrapped)
            .map_err(|_| TryFromSurjError);
        assert_eq!(cur_composed, OrderPresSurj::try_from((cur_test.clone(), 0)));

        cur_test = vec![1];
        cur_result = Err(TryFromSurjError);
        assert_eq!(cur_result, OrderPresSurj::try_from((cur_test, 0)));

        cur_test = vec![2];
        cur_result = Err(TryFromSurjError);
        assert_eq!(cur_result, OrderPresSurj::try_from((cur_test, 0)));

        cur_test = vec![0, 1, 2];

        cur_result = Ok([0, 0, 0].into());
        assert_eq!(cur_result, OrderPresSurj::try_from((cur_test.clone(), 0)));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }
        assert_eq!(cur_result_unwrapped.domain(), 3);
        assert_eq!(cur_result_unwrapped.codomain(), 3);
        let cur_composed_2 = cur_result_unwrapped.compose(&cur_result_unwrapped).unwrap();
        assert_eq!(cur_composed_2, cur_result_unwrapped);

        cur_test = vec![0, 2, 1];
        cur_result = Err(TryFromSurjError);
        assert_eq!(cur_result, OrderPresSurj::try_from((cur_test, 0)));

        cur_test = vec![0, 1, 1, 2, 3, 3, 3, 4];
        cur_result = Ok([0, 1, 0, 2, 0].into());
        assert_eq!(cur_result, OrderPresSurj::try_from((cur_test.clone(), 0)));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }
        assert_eq!(cur_result_unwrapped.domain(), 8);
        assert_eq!(cur_result_unwrapped.codomain(), 5);

        let compose_3_after: OrderPresSurj = [1, 2].into();
        let compose_3_exp: OrderPresSurj = [2, 4].into();
        let cur_composed_3 = cur_result_unwrapped.compose(&compose_3_after).unwrap();
        assert_eq!(cur_composed_3, compose_3_exp);
    }

    #[test]
    fn ord_inj_conversion() {
        use super::{FinSetMap, OrderPresInj, TryFromInjError};
        use crate::category::Composable;
        let mut cur_test: FinSetMap = vec![];
        let mut cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![],
        });
        assert_eq!(cur_result, OrderPresInj::try_from((cur_test.clone(), 0)));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }
        assert_eq!(cur_result_unwrapped.domain(), 0);
        assert_eq!(cur_result_unwrapped.codomain(), 0);

        cur_test = vec![0];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![1],
        });
        assert_eq!(cur_result, OrderPresInj::try_from((cur_test.clone(), 0)));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }
        assert_eq!(cur_result_unwrapped.domain(), 1);
        assert_eq!(cur_result_unwrapped.codomain(), 1);

        cur_test = vec![1];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![0, 1, 1],
        });
        assert_eq!(cur_result, OrderPresInj::try_from((cur_test.clone(), 0)));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }
        assert_eq!(cur_result_unwrapped.domain(), 1);
        assert_eq!(cur_result_unwrapped.codomain(), 2);

        cur_test = vec![2];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![0, 2, 1],
        });
        assert_eq!(cur_result, OrderPresInj::try_from((cur_test.clone(), 0)));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }
        assert_eq!(cur_result_unwrapped.domain(), 1);
        assert_eq!(cur_result_unwrapped.codomain(), 3);

        cur_test = vec![0, 1, 2];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![3],
        });
        assert_eq!(cur_result, OrderPresInj::try_from((cur_test.clone(), 0)));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }
        assert_eq!(cur_result_unwrapped.domain(), 3);
        assert_eq!(cur_result_unwrapped.codomain(), 3);

        cur_test = vec![0, 2, 1];
        cur_result = Err(TryFromInjError);
        assert_eq!(cur_result, OrderPresInj::try_from((cur_test, 0)));

        cur_test = vec![0, 1, 1, 2, 3, 3, 3, 4];
        cur_result = Err(TryFromInjError);
        assert_eq!(cur_result, OrderPresInj::try_from((cur_test, 0)));

        let leftovers = 23;
        cur_test = vec![0, 1, 2, 4, 5, 8, 9, 11];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![3, 1, 2, 2, 2, 1, 1, leftovers],
        });
        assert_eq!(
            cur_result,
            OrderPresInj::try_from((cur_test.clone(), leftovers))
        );
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }
        assert_eq!(cur_result_unwrapped.domain(), 8);
        assert_eq!(cur_result_unwrapped.codomain(), 12 + leftovers);
    }

    #[test]
    fn monotone_epi_mono_fact() {
        use crate::finset::{monotone_epi_mono_fact, FinSetMap};
        let mut cur_test: FinSetMap = vec![0, 1, 1, 1, 2, 3, 4, 7, 8, 9, 11];
        let mut exp_surj: FinSetMap = vec![0, 1, 1, 1, 2, 3, 4, 5, 6, 7, 8];
        let mut exp_inj: FinSetMap = vec![0, 1, 2, 3, 4, 7, 8, 9, 11];
        let (tested_surj, tested_inj) = monotone_epi_mono_fact(cur_test);
        assert_eq!(exp_surj, tested_surj);
        assert_eq!(exp_inj, tested_inj);

        cur_test = vec![];
        exp_surj = vec![];
        exp_inj = vec![];
        let (tested_surj, tested_inj) = monotone_epi_mono_fact(cur_test);
        assert_eq!(exp_surj, tested_surj);
        assert_eq!(exp_inj, tested_inj);

        cur_test = vec![3];
        exp_surj = vec![0];
        exp_inj = vec![3];
        let (tested_surj, tested_inj) = monotone_epi_mono_fact(cur_test);
        assert_eq!(exp_surj, tested_surj);
        assert_eq!(exp_inj, tested_inj);
    }

    #[test]
    fn permutation_test() {
        use crate::finset::{permutation_sort, Decomposition, FinSetMap};
        use crate::symmetric_monoidal::SymmetricMonoidalDiscreteMorphism;
        use permutations::Permutation;
        let mut cur_test: FinSetMap = vec![0, 1, 1, 1, 2, 3, 4, 7, 8, 9, 11];
        let mut exp_sorted = vec![0, 1, 1, 1, 2, 3, 4, 7, 8, 9, 11];
        let mut exp_perm = Permutation::identity(cur_test.len());
        let mut cur_perm = permutation_sort(&mut cur_test);
        assert_eq!(cur_test, exp_sorted);
        assert_eq!(cur_perm, exp_perm);
        assert_eq!(
            cur_perm.permute(&[0, 1, 1, 1, 2, 3, 4, 7, 8, 9, 11]),
            cur_test
        );
        let decomp = Decomposition::from_permutation(cur_perm.clone(), cur_test.len(), true);
        for idx in 0..cur_test.len() {
            let after_decomp = decomp.apply(idx);
            let after_cur_perm = cur_perm.apply(idx);
            assert_eq!(after_decomp, after_cur_perm);
        }

        cur_test = vec![1, 0];
        exp_sorted = vec![0, 1];
        exp_perm = Permutation::rotation_left(2, 1);
        cur_perm = permutation_sort(&mut cur_test);
        assert_eq!(cur_test, exp_sorted);
        assert_eq!(cur_perm, exp_perm);
        assert_eq!(cur_perm.permute(&[1, 0]), cur_test);
        let decomp = Decomposition::from_permutation(cur_perm.clone(), cur_test.len(), true);
        for idx in 0..cur_test.len() {
            let after_decomp = decomp.apply(idx);
            let after_cur_perm = cur_perm.apply(idx);
            assert_eq!(after_decomp, after_cur_perm);
        }

        cur_test = vec![2, 1, 0];
        exp_sorted = vec![0, 1, 2];
        exp_perm = Permutation::transposition(3, 0, 2);
        cur_perm = permutation_sort(&mut cur_test);
        assert_eq!(cur_test, exp_sorted);
        assert_eq!(cur_perm, exp_perm);
        assert_eq!(cur_perm.permute(&[2, 1, 0]), cur_test);
        let decomp = Decomposition::from_permutation(cur_perm.clone(), cur_test.len(), true);
        for idx in 0..cur_test.len() {
            let after_decomp = decomp.apply(idx);
            let after_cur_perm = cur_perm.apply(idx);
            assert_eq!(after_decomp, after_cur_perm);
        }

        cur_test = vec![2, 0, 1];
        exp_sorted = vec![0, 1, 2];
        exp_perm = Permutation::rotation_left(3, 1);
        cur_perm = permutation_sort(&mut cur_test);
        assert_eq!(cur_test, exp_sorted);
        assert_eq!(cur_perm, exp_perm);
        assert_eq!(cur_perm.permute(&[2, 0, 1]), cur_test);
        let decomp = Decomposition::from_permutation(cur_perm.clone(), cur_test.len(), true);
        for idx in 0..cur_test.len() {
            let after_decomp = decomp.apply(idx);
            let after_cur_perm = cur_perm.apply(idx);
            assert_eq!(after_decomp, after_cur_perm);
        }

        cur_test = vec![2, 0, 0, 1, 1];
        exp_sorted = vec![0, 0, 1, 1, 2];
        exp_perm = Permutation::rotation_left(5, 1);
        cur_perm = permutation_sort(&mut cur_test);
        assert_eq!(cur_test, exp_sorted);
        assert_eq!(cur_perm, exp_perm);
        assert_eq!(cur_perm.permute(&[2, 0, 0, 1, 1]), cur_test);
        let decomp = Decomposition::from_permutation(cur_perm.clone(), cur_test.len(), true);
        for idx in 0..cur_test.len() {
            let after_decomp = decomp.apply(idx);
            let after_cur_perm = cur_perm.apply(idx);
            assert_eq!(after_decomp, after_cur_perm);
        }
    }

    #[test]
    fn decomposition() {
        use crate::finset::{Decomposition, FinSetMap, OrderPresInj, OrderPresSurj};
        use permutations::Permutation;
        for leftovers in [0, 5, 7] {
            let cur_test: FinSetMap = vec![0, 1, 1, 1, 2, 3, 4, 7, 8, 9, 11, 20, 18, 19];
            let exp_perm =
                Permutation::try_from(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 13, 11, 12]).unwrap();
            let exp_surj: OrderPresSurj = [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].into();
            let exp_inj = OrderPresInj {
                counts_iden_unit_alternating: if leftovers > 0 {
                    vec![5, 2, 3, 1, 1, 6, 3, leftovers]
                } else {
                    vec![5, 2, 3, 1, 1, 6, 3]
                },
            };
            let cur_res = Decomposition::try_from((cur_test.clone(), leftovers));
            #[allow(clippy::assertions_on_constants)]
            if let Ok(cur_decomp) = cur_res {
                assert_eq!(exp_perm, cur_decomp.permutation_part);
                assert_eq!(exp_surj, cur_decomp.order_preserving_surjection);
                assert_eq!(exp_inj, cur_decomp.order_preserving_injection);
                #[allow(clippy::needless_range_loop)]
                for test_pt in 0..cur_test.len() {
                    let actual_dest = cur_test[test_pt];
                    let apparent_dest = cur_decomp.apply(test_pt);
                    assert_eq!(apparent_dest, actual_dest);
                }
            } else {
                assert!(false, "All maps of finite sets decompose");
            }
        }
    }

    #[allow(clippy::similar_names)]
    #[test]
    fn two_decompositions() {
        use crate::category::Composable;
        use crate::finset::Decomposition;
        use rand::Rng;

        let fin_set_size: usize = 20;
        let mut rng = rand::thread_rng();
        let trial_num = 10;

        for _ in 0..trial_num {
            let first_int_map: Vec<_> = (0..fin_set_size)
                .map(|_| rng.gen_range(0..fin_set_size))
                .collect();
            let second_int_map: Vec<_> = (0..fin_set_size)
                .map(|_| rng.gen_range(0..fin_set_size))
                .collect();
            let max_first = *first_int_map.iter().max().unwrap();
            let leftover_needed = (fin_set_size - max_first - 1).max(0);
            let decomp_1 =
                Decomposition::try_from((first_int_map.clone(), leftover_needed)).unwrap();
            assert_eq!(decomp_1.domain(), fin_set_size);
            assert_eq!(decomp_1.codomain(), fin_set_size);
            let (decomp_1_ord, decomp_1_left) = decomp_1.to_ordinary();
            assert_eq!(decomp_1_ord, first_int_map);
            assert_eq!(decomp_1_left, leftover_needed);
            let decomp_2 = Decomposition::try_from((second_int_map.clone(), 0)).unwrap();
            let actual_codomain = *second_int_map.iter().max().unwrap() + 1;
            assert_eq!(decomp_2.domain(), fin_set_size);
            assert_eq!(decomp_2.codomain(), actual_codomain);
            let (decomp_2_ord, decomp_2_left) = decomp_2.to_ordinary();
            assert_eq!(decomp_2_ord, second_int_map);
            assert_eq!(decomp_2_left, 0);
            let decomp_12 = decomp_1.compose(&decomp_2).unwrap();
            assert_eq!(decomp_12.domain(), fin_set_size);
            assert_eq!(decomp_12.codomain(), actual_codomain);
            #[allow(clippy::needless_range_loop)]
            for idx in 0..fin_set_size {
                let after_first = first_int_map[idx];
                assert_eq!(decomp_1.apply(idx), after_first);
                let after_second = second_int_map[after_first];
                assert_eq!(decomp_2.apply(after_first), after_second);
                assert_eq!(decomp_12.apply(idx), after_second);
            }
        }
    }

    #[test]
    fn cycle_test() {
        use crate::finset::from_cycle;
        use itertools::Itertools;
        use rand::distributions::Uniform;
        use rand::Rng;

        let fin_set_size: usize = 20;
        let mut rng = rand::thread_rng();
        let u = Uniform::new(0, fin_set_size);
        for _ in 0..10 {
            let cycle_len = rng.sample(u);
            let cycle = (0..cycle_len).map(|_| rng.sample(u)).collect_vec();
            let mut cycle_sorted = cycle.clone();
            cycle_sorted.sort_unstable();
            cycle_sorted.dedup();
            if cycle_sorted.len() < cycle.len() {
                continue;
            }
            let p = from_cycle(fin_set_size, &cycle);
            for (a, b) in cycle.iter().tuple_windows() {
                assert_eq!(
                    p.apply(*a),
                    *b,
                    "{:?} should take {} to {} but it is {:?}",
                    cycle,
                    *a,
                    *b,
                    p
                );
            }
            break;
        }
    }
}
