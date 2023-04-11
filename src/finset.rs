use std::{collections::HashSet, error, fmt};

use permutations::Permutation;

use crate::category::{Composable, HasIdentity};
use crate::monoidal::{Monoidal, MonoidalMorphism};
use crate::symmetric_monoidal::SymmetricMonoidalDiscreteMorphism;
use crate::utils::position_max;

pub type FinSetMap = Vec<usize>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderPresSurj {
    preimage_card_minus_1: Vec<usize>,
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
    fn compose(&self, other: &Self) -> Result<Self, String> {
        if Self::composable(self, other).is_err() {
            let self_codomain = self.codomain();
            let other_domain = other.domain();
            return Err(format!(
                "Not composable. The codomain of self was {}. The domain of other was {}",
                self_codomain, other_domain
            ));
        }
        let my_codomain = other.codomain();
        let mut answer = Vec::with_capacity(my_codomain);
        let mut self_idx = 0;
        for idx in 0..my_codomain {
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
        // todo test
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
    fn to_ordinary(&self) -> FinSetMap {
        let domain_size: usize = self.domain();
        let mut answer = Vec::with_capacity(domain_size);
        for (cur_target, v) in self.preimage_card_minus_1.iter().enumerate() {
            for _ in 0..(v + 1) {
                answer.push(cur_target);
            }
        }
        answer
    }

    fn apply(&self, test_pt: usize) -> usize {
        self.to_ordinary()[test_pt]
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
    fn compose(&self, other: &Self) -> Result<Self, String> {
        if Self::composable(self, other).is_err() {
            let self_codomain = self.codomain();
            let other_domain = other.domain();
            return Err(format!(
                "Not composable. The codomain of self was {}. The domain of other was {}",
                self_codomain, other_domain
            ));
        }
        let ord_self = self.to_ordinary();
        let ord_other = other.to_ordinary();
        let composite = (0..ord_self.len())
            .map(|s| ord_other[ord_self[s]])
            .collect::<Vec<usize>>();
        OrderPresInj::try_from(composite).map_err(|_| "???".to_string())
        //todo test
    }

    fn domain(&self) -> usize {
        self.counts_iden_unit_alternating
            .iter()
            .enumerate()
            .map(|(n, v)| (n % 2) * v)
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
    fn to_ordinary(&self) -> FinSetMap {
        let domain_size: usize = self.domain();
        let mut answer = Vec::with_capacity(domain_size);
        let mut cur_target = 0;
        for (n, v) in self.counts_iden_unit_alternating.iter().enumerate() {
            if n % 2 == 0 {
                for _ in 0..*v {
                    answer.push(cur_target);
                    cur_target += 1;
                }
            } else {
                cur_target += v;
            }
        }
        answer
    }

    fn apply(&self, test_pt: usize) -> usize {
        self.to_ordinary()[test_pt]
    }

    pub fn iden_unit_counts(&self) -> Vec<usize> {
        self.counts_iden_unit_alternating.clone()
    }
}

fn is_monotonic_inc<T: Ord, I>(mut my_iter: I, prev_elt: Option<T>) -> bool
where
    I: Iterator<Item = T>,
{
    let current = my_iter.next();
    if let Some(real_current) = current {
        if let Some(real_prev_elt) = prev_elt {
            if real_prev_elt > real_current {
                return false;
            }
        }
        is_monotonic_inc(my_iter, Some(real_current))
    } else {
        true
    }
}

fn is_surjective(v: &[usize]) -> bool {
    let pos_max = position_max(v);
    if let Some(max_val) = pos_max.map(|z| v[z]) {
        if v.len() < max_val + 1 {
            return false;
        }
        let mut seen_elts = HashSet::new();
        for cur_v in v {
            seen_elts.insert(*cur_v);
        }
        seen_elts.len() == max_val + 1
    } else {
        // empty set to empty set
        true
    }
}

fn is_injective(v: &[usize]) -> bool {
    let pos_max = position_max(v);
    if let Some(max_val) = pos_max.map(|z| v[z]) {
        if v.len() > max_val + 1 {
            return false;
        }
        let mut seen_elts = HashSet::with_capacity(v.len());
        for cur_v in v {
            if seen_elts.contains(cur_v) {
                return false;
            }
            seen_elts.insert(*cur_v);
        }
        true
    } else {
        // empty set to empty set
        true
    }
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

impl TryFrom<FinSetMap> for OrderPresSurj {
    type Error = TryFromSurjError;
    fn try_from(v: FinSetMap) -> Result<OrderPresSurj, TryFromSurjError> {
        if is_monotonic_inc(v.iter(), None) && is_surjective(&v) {
            if v.is_empty() {
                return Ok(OrderPresSurj {
                    preimage_card_minus_1: vec![],
                });
            }
            let mut cur_i = 0;
            let mut count_of_cur_i = 0;
            let my_max = v[v.len() - 1];
            let mut preimage_card_minus_1 = Vec::with_capacity(my_max);
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
            Ok(OrderPresSurj {
                preimage_card_minus_1,
            })
        } else {
            Err(TryFromSurjError)
        }
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

impl TryFrom<FinSetMap> for OrderPresInj {
    type Error = TryFromInjError;
    fn try_from(v: FinSetMap) -> Result<OrderPresInj, TryFromInjError> {
        if is_monotonic_inc(v.iter(), None) && is_injective(&v) {
            if v.is_empty() {
                return Ok(OrderPresInj {
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
            }
            counts_iden_unit_alternating.shrink_to_fit();
            Ok(OrderPresInj {
                counts_iden_unit_alternating,
            })
        } else {
            Err(TryFromInjError)
        }
    }
}
impl error::Error for TryFromInjError {}

fn permutation_sort<T: Ord>(x: &mut [T]) -> Permutation {
    let mut answer: FinSetMap = (0..x.len()).collect();
    answer.sort_by(|a, b| x[*a].cmp(&x[*b]));
    x.sort();
    Permutation::try_from(answer).unwrap()
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
    fn compose(&self, other: &Self) -> Result<Self, String> {
        if Self::composable(self, other).is_err() {
            let self_codomain = self.codomain();
            let other_domain = other.domain();
            return Err(format!(
                "Not composable. The codomain of self was {}. The domain of other was {}",
                self_codomain, other_domain
            ));
        }
        let ord_self = self.to_ordinary();
        let ord_other = other.to_ordinary();
        let composite = (0..ord_self.len())
            .map(|s| ord_other[ord_self[s]])
            .collect::<Vec<usize>>();
        Decomposition::try_from(composite).map_err(|_| "???".to_string())
        //todo test
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

    fn from_permutation(p: Permutation, my_type: usize, _: bool) -> Self {
        assert_eq!(p.len(), my_type);
        let _answer = Self {
            permutation_part: p,
            order_preserving_injection: OrderPresInj::identity(&my_type),
            order_preserving_surjection: OrderPresSurj::identity(&my_type),
        };
        todo!("might be p.inv() instead")
    }
}

impl Decomposition {
    fn apply(&self, test_pt: usize) -> usize {
        let dest_after_perm = self.permutation_part.apply(test_pt);
        let dest_after_surj = self.order_preserving_surjection.apply(dest_after_perm);
        self.order_preserving_injection.apply(dest_after_surj)
    }

    fn to_ordinary(&self) -> FinSetMap {
        (0..self.domain())
            .map(|z| self.apply(z))
            .collect::<FinSetMap>()
    }

    pub fn get_parts(&self) -> (&Permutation, &OrderPresSurj, &OrderPresInj) {
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

impl TryFrom<FinSetMap> for Decomposition {
    type Error = TryFromFinSetError;
    fn try_from(v: FinSetMap) -> Result<Decomposition, TryFromFinSetError> {
        if is_monotonic_inc(v.iter(), None) {
            let permutation_part = Permutation::identity(v.len());
            let (epic_part, monic_part) = monotone_epi_mono_fact(v);
            let order_preserving_surjection =
                OrderPresSurj::try_from(epic_part).map_err(|_| TryFromFinSetError)?;
            let order_preserving_injection =
                OrderPresInj::try_from(monic_part).map_err(|_| TryFromFinSetError)?;
            Ok(Decomposition {
                permutation_part,
                order_preserving_surjection,
                order_preserving_injection,
            })
        } else {
            let mut v_clone = v;
            let permutation_part = permutation_sort(&mut v_clone).inv();
            let (epic_part, monic_part) = monotone_epi_mono_fact(v_clone);
            let order_preserving_surjection =
                OrderPresSurj::try_from(epic_part).map_err(|_| TryFromFinSetError)?;
            let order_preserving_injection =
                OrderPresInj::try_from(monic_part).map_err(|_| TryFromFinSetError)?;
            Ok(Decomposition {
                permutation_part,
                order_preserving_surjection,
                order_preserving_injection,
            })
        }
    }
}
impl error::Error for TryFromFinSetError {}

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
    fn monotonicity() {
        use crate::finset::is_monotonic_inc;
        let mut cur_test: Vec<i8> = vec![];
        assert!(is_monotonic_inc(cur_test.iter(), None));
        cur_test = vec![1];
        assert!(is_monotonic_inc(cur_test.iter(), None));
        cur_test = vec![-1];
        assert!(is_monotonic_inc(cur_test.iter(), None));
        cur_test = vec![-124];
        assert!(is_monotonic_inc(cur_test.iter(), None));
        cur_test = vec![1, 2];
        assert!(is_monotonic_inc(cur_test.iter(), None));
        cur_test = vec![2, 1];
        assert!(!is_monotonic_inc(cur_test.iter(), None));
        cur_test = vec![3, 1, 2];
        assert!(!is_monotonic_inc(cur_test.iter(), None));
        cur_test = vec![1, 1, 2];
        assert!(is_monotonic_inc(cur_test.iter(), None));
    }

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
        use crate::finset::{FinSetMap, OrderPresSurj, TryFromSurjError};
        let mut cur_test: FinSetMap = vec![];
        let mut cur_result = Ok(OrderPresSurj {
            preimage_card_minus_1: vec![],
        });
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test));

        cur_test = vec![0];
        cur_result = Ok(OrderPresSurj {
            preimage_card_minus_1: vec![0],
        });
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test.clone()));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }

        cur_test = vec![1];
        cur_result = Err(TryFromSurjError);
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test));

        cur_test = vec![2];
        cur_result = Err(TryFromSurjError);
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test));

        cur_test = vec![0, 1, 2];
        cur_result = Ok(OrderPresSurj {
            preimage_card_minus_1: vec![0, 0, 0],
        });
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test.clone()));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }

        cur_test = vec![0, 2, 1];
        cur_result = Err(TryFromSurjError);
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test));

        cur_test = vec![0, 1, 1, 2, 3, 3, 3, 4];
        cur_result = Ok(OrderPresSurj {
            preimage_card_minus_1: vec![0, 1, 0, 2, 0],
        });
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test.clone()));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }
    }

    #[test]
    fn ord_inj_conversion() {
        use crate::finset::{FinSetMap, OrderPresInj, TryFromInjError};
        let mut cur_test: FinSetMap = vec![];
        let mut cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![],
        });
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test.clone()));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }

        cur_test = vec![0];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![1],
        });
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test.clone()));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }

        cur_test = vec![1];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![0, 1, 1],
        });
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test.clone()));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }

        cur_test = vec![2];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![0, 2, 1],
        });
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test.clone()));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }

        cur_test = vec![0, 1, 2];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![3],
        });
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test.clone()));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }

        cur_test = vec![0, 2, 1];
        cur_result = Err(TryFromInjError);
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test));

        cur_test = vec![0, 1, 1, 2, 3, 3, 3, 4];
        cur_result = Err(TryFromInjError);
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test));

        cur_test = vec![0, 1, 2, 4, 5, 8, 9, 11];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![3, 1, 2, 2, 2, 1, 1],
        });
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test.clone()));
        let cur_result_unwrapped = cur_result.unwrap();
        for (n, v) in cur_test.iter().enumerate() {
            let dest_test_pt = cur_result_unwrapped.apply(n);
            assert_eq!(dest_test_pt, *v);
        }
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
        use crate::finset::{permutation_sort, FinSetMap};
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

        cur_test = vec![1, 0];
        exp_sorted = vec![0, 1];
        exp_perm = Permutation::rotation_left(2, 1);
        cur_perm = permutation_sort(&mut cur_test);
        assert_eq!(cur_test, exp_sorted);
        assert_eq!(cur_perm, exp_perm);
        assert_eq!(cur_perm.permute(&[1, 0]), cur_test);

        cur_test = vec![2, 1, 0];
        exp_sorted = vec![0, 1, 2];
        exp_perm = Permutation::transposition(3, 0, 2);
        cur_perm = permutation_sort(&mut cur_test);
        assert_eq!(cur_test, exp_sorted);
        assert_eq!(cur_perm, exp_perm);
        assert_eq!(cur_perm.permute(&[2, 1, 0]), cur_test);

        cur_test = vec![2, 0, 1];
        exp_sorted = vec![0, 1, 2];
        exp_perm = Permutation::rotation_left(3, 1);
        cur_perm = permutation_sort(&mut cur_test);
        assert_eq!(cur_test, exp_sorted);
        assert_eq!(cur_perm, exp_perm);
        assert_eq!(cur_perm.permute(&[2, 0, 1]), cur_test);

        cur_test = vec![2, 0, 0, 1, 1];
        exp_sorted = vec![0, 0, 1, 1, 2];
        exp_perm = Permutation::rotation_left(5, 1);
        cur_perm = permutation_sort(&mut cur_test);
        assert_eq!(cur_test, exp_sorted);
        assert_eq!(cur_perm, exp_perm);
        assert_eq!(cur_perm.permute(&[2, 0, 0, 1, 1]), cur_test);
    }

    #[test]
    fn decomposition() {
        use crate::finset::{Decomposition, FinSetMap, OrderPresInj, OrderPresSurj};
        let cur_test: FinSetMap = vec![0, 1, 1, 1, 2, 3, 4, 7, 8, 9, 11, 20, 18, 19];
        let exp_surj = OrderPresSurj {
            preimage_card_minus_1: vec![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        };
        let exp_inj = OrderPresInj {
            counts_iden_unit_alternating: vec![5, 2, 3, 1, 1, 6, 3],
        };
        let cur_res = Decomposition::try_from(cur_test.clone());
        if let Ok(cur_decomp) = cur_res {
            assert_eq!(exp_surj, cur_decomp.order_preserving_surjection);
            assert_eq!(exp_inj, cur_decomp.order_preserving_injection);
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
