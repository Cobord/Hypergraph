use std::{collections::HashSet, error, fmt};

use permutations::Permutation;

use crate::utils::position_max;
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct OrderPresSurj {
    preimage_card_minus_1: Vec<usize>,
}
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
struct OrderPresInj {
    counts_iden_unit_alternating: Vec<usize>,
}

#[allow(dead_code)]
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

#[allow(dead_code)]
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

#[allow(dead_code)]
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
struct TryFromSurjError;
impl fmt::Display for TryFromSurjError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ill-formed slice to order preserving surjection conversion attempted"
        )
    }
}

impl TryFrom<Vec<usize>> for OrderPresSurj {
    type Error = TryFromSurjError;
    fn try_from(v: Vec<usize>) -> Result<OrderPresSurj, TryFromSurjError> {
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
struct TryFromInjError;
impl fmt::Display for TryFromInjError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ill-formed slice to order preserving injection conversion attempted"
        )
    }
}

impl TryFrom<Vec<usize>> for OrderPresInj {
    type Error = TryFromInjError;
    fn try_from(v: Vec<usize>) -> Result<OrderPresInj, TryFromInjError> {
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

#[allow(dead_code)]
struct Decomposition {
    permutation_part: Permutation,
    order_preserving_surjection: OrderPresSurj,
    order_preserving_injection: OrderPresInj,
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct TryFromFinSetError;
impl fmt::Display for TryFromFinSetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ill-formed slice to order preserving map conversion attempted"
        )
    }
}

impl TryFrom<Vec<usize>> for Decomposition {
    type Error = TryFromFinSetError;
    #[allow(clippy::if_same_then_else)]
    fn try_from(v: Vec<usize>) -> Result<Decomposition, TryFromFinSetError> {
        if is_monotonic_inc(v.iter(), None) {
            todo!()
        } else {
            todo!()
        }
    }
}
impl error::Error for TryFromFinSetError {}

#[allow(dead_code)]
fn monotone_epi_mono_fact(v: Vec<usize>) -> (Vec<usize>,Vec<usize>) {
    if v.is_empty() {
        return (vec![],vec![]);
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
        cur_index+=1;
        if cur_item==current_image_number_in_tgt {
            surj_part[cur_index] = current_image_number;
        } else {
            current_image_number+=1;
            current_image_number_in_tgt = cur_item;
            surj_part[cur_index] = current_image_number;
            inj_part.push(*cur_item);
        }
    }
    inj_part.shrink_to_fit();
    (surj_part,inj_part)
}

mod test {

    #[test]
    fn monotonicity() {
        use crate::finset::is_monotonic_inc;
        let mut cur_test = vec![];
        assert!(is_monotonic_inc(cur_test.iter(), None));
        cur_test = vec![1];
        assert!(is_monotonic_inc(cur_test.iter(), None));
        cur_test = vec![-1];
        assert!(is_monotonic_inc(cur_test.iter(), None));
        cur_test = vec![-12490];
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
        use crate::finset::is_surjective;
        let mut cur_test: Vec<usize> = vec![];
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
        use crate::finset::is_injective;
        let mut cur_test: Vec<usize> = vec![];
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
        use crate::finset::{OrderPresSurj, TryFromSurjError};
        let mut cur_test: Vec<usize> = vec![];
        let mut cur_result = Ok(OrderPresSurj {
            preimage_card_minus_1: vec![],
        });
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test));

        cur_test = vec![0];
        cur_result = Ok(OrderPresSurj {
            preimage_card_minus_1: vec![0],
        });
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test));

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
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test));

        cur_test = vec![0, 2, 1];
        cur_result = Err(TryFromSurjError);
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test));

        cur_test = vec![0, 1, 1, 2, 3, 3, 3, 4];
        cur_result = Ok(OrderPresSurj {
            preimage_card_minus_1: vec![0, 1, 0, 2, 0],
        });
        assert_eq!(cur_result, OrderPresSurj::try_from(cur_test));
    }

    #[test]
    fn ord_inj_conversion() {
        use crate::finset::{OrderPresInj, TryFromInjError};
        let mut cur_test: Vec<usize> = vec![];
        let mut cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![],
        });
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test));

        cur_test = vec![0];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![1],
        });
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test));

        cur_test = vec![1];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![0, 1, 1],
        });
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test));

        cur_test = vec![2];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![0, 2, 1],
        });
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test));

        cur_test = vec![0, 1, 2];
        cur_result = Ok(OrderPresInj {
            counts_iden_unit_alternating: vec![3],
        });
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test));

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
        assert_eq!(cur_result, OrderPresInj::try_from(cur_test));
    }

    #[test]
    fn monotone_epi_mono_fact() {
        use crate::finset::{monotone_epi_mono_fact};
        let mut cur_test: Vec<usize> = vec![0,1,1,1,2,3,4,7,8,9,11];
        let mut exp_surj = vec![0,1,1,1,2,3,4,5,6,7,8];
        let mut exp_inj = vec![0,1,2,3,4,7,8,9,11];
        let (tested_surj,tested_inj) = monotone_epi_mono_fact(cur_test);
        assert_eq!(exp_surj,tested_surj);
        assert_eq!(exp_inj,tested_inj);

        cur_test = vec![];
        exp_surj = vec![];
        exp_inj = vec![];
        let (tested_surj,tested_inj) = monotone_epi_mono_fact(cur_test);
        assert_eq!(exp_surj,tested_surj);
        assert_eq!(exp_inj,tested_inj);

        cur_test = vec![3];
        exp_surj = vec![0];
        exp_inj = vec![3];
        let (tested_surj,tested_inj) = monotone_epi_mono_fact(cur_test);
        assert_eq!(exp_surj,tested_surj);
        assert_eq!(exp_inj,tested_inj);


    }
}
