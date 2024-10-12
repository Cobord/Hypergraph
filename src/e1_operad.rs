use std::ops::MulAssign;

use itertools::Itertools;
use num::One;
use rand::{rngs::ThreadRng, Rng};

use crate::{
    category::HasIdentity,
    operadic::{Operadic, OperadicError},
};

type IntervalCoord = f32;
type CoalesceError = String;

#[allow(dead_code)]
pub struct E1 {
    arity: usize,
    sub_intervals: Vec<(IntervalCoord, IntervalCoord)>,
}

impl E1 {
    pub fn new(sub_intervals: Vec<(IntervalCoord, IntervalCoord)>, overlap_check: bool) -> Self {
        /*
        new n-ary operation in E1 operad where n is the length of input
        */
        for (a, b) in &sub_intervals {
            assert!(
                *a < *b && 0.0 <= *a && *b <= 1.0,
                "Each subinterval must be an interval contained in (0,1)"
            );
        }
        if overlap_check {
            let mut new_sub_intervals = sub_intervals.clone();
            new_sub_intervals.sort_by(|i1, i2| i1.0.partial_cmp(&i2.0).unwrap());
            for ((a, b), (c, d)) in new_sub_intervals.iter().tuple_windows() {
                assert!(*b < *c || *d < *a, "The subintervals cannot overlap");
            }
            Self {
                arity: sub_intervals.len(),
                sub_intervals: new_sub_intervals,
            }
        } else {
            Self {
                arity: sub_intervals.len(),
                sub_intervals,
            }
        }
    }

    #[allow(dead_code)]
    pub fn random(cur_arity: usize, rng: &mut ThreadRng) -> Self {
        let mut sub_ints: Vec<IntervalCoord> = (0..2 * cur_arity)
            .map(|_| rng.gen_range(0.0..1.0))
            .collect();
        sub_ints.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        let sub_intervals: Vec<(IntervalCoord, IntervalCoord)> = sub_ints
            .chunks_exact(2)
            .map(|chunk| (chunk[0], chunk[1]))
            .collect();
        Self::new(sub_intervals, false)
    }

    fn canonicalize(&mut self) {
        self.sub_intervals
            .sort_by(|i1, i2| i1.0.partial_cmp(&i2.0).unwrap());
    }

    #[allow(dead_code)]
    pub fn go_to_monoid<M: One + MulAssign>(
        &mut self,
        interval_fn: impl Fn((IntervalCoord, IntervalCoord)) -> M,
    ) -> M {
        self.canonicalize();
        let mut acc = M::one();
        self.sub_intervals.iter().for_each(|x| {
            acc *= interval_fn(*x);
        });
        acc
    }

    #[allow(dead_code)]
    pub fn coalesce_boxes(
        &mut self,
        all_in_this_interval: (IntervalCoord, IntervalCoord),
    ) -> Result<(), CoalesceError> {
        self.can_coalesce_boxes(all_in_this_interval)?;
        let (a, b) = all_in_this_interval;
        self.sub_intervals.retain(|(c, d)| *d <= a || *c >= b);
        self.sub_intervals.push((a, b));
        self.arity = self.sub_intervals.len();
        Ok(())
    }

    pub fn can_coalesce_boxes(
        &self,
        all_in_this_interval: (IntervalCoord, IntervalCoord),
    ) -> Result<(), CoalesceError> {
        let (a, b) = all_in_this_interval;
        if a >= b || a < 0.0 || b > 1.0 {
            return Err(
                "The coalescing interval must be an interval contained in (0,1)".to_string(),
            );
        }
        for cur_pair in &self.sub_intervals {
            let (c, d) = cur_pair;
            let contained_within = *c >= a && *d <= b;
            let disjoint_from = *d <= a || *c >= b;
            let bad_config = !(contained_within || disjoint_from);
            if bad_config {
                return Err("All subintervals must be either contained within or disjoint from the coalescing interval".to_string());
            }
        }
        Ok(())
    }

    #[allow(dead_code)]
    pub fn min_closeness(&self) -> Option<IntervalCoord> {
        if self.arity < 2 {
            return None;
        }
        assert!(
            self.sub_intervals.iter().is_sorted_by(|i1, i2| i1
                .0
                .partial_cmp(&i2.0)
                .expect("No incomparable IntervalCoord issues with NaN etc")
                .is_le()),
            "Should be in canonical form already"
        );
        let mut min_closeness = 1.0;
        for (i1, i2) in self.sub_intervals.iter().tuple_windows() {
            let cur_closeness = i2.0 - i1.1;
            if cur_closeness < min_closeness {
                min_closeness = cur_closeness;
            }
        }
        Some(min_closeness)
    }

    pub fn extract_sub_intervals(mut self) -> Vec<(IntervalCoord, IntervalCoord)> {
        self.canonicalize();
        self.sub_intervals
    }
}

impl Operadic<usize> for E1 {
    fn operadic_substitution(
        &mut self,
        which_input: usize,
        other_obj: Self,
    ) -> Result<(), OperadicError> {
        if which_input >= self.arity {
            return Err(format!(
                "There aren't enough inputs to graft onto the {}'th one",
                which_input + 1
            )
            .into());
        }
        self.canonicalize();
        let (a, b) = self.sub_intervals[which_input];
        let length_subbed = b - a;
        let mut new_subs = other_obj
            .sub_intervals
            .into_iter()
            .map(|(c, d)| (c * length_subbed + a, d * length_subbed + a));
        let first_new_subs = new_subs.next();
        if let Some(actual_first) = first_new_subs {
            self.sub_intervals[which_input] = actual_first;
            self.sub_intervals.extend(new_subs);
            self.arity += other_obj.arity - 1;
        } else {
            _ = self.sub_intervals.swap_remove(which_input);
            self.arity -= 1;
        }
        Ok(())
    }
}

impl HasIdentity<()> for E1 {
    fn identity((): &()) -> Self {
        Self {
            arity: 1,
            sub_intervals: vec![(0.0, 1.0)],
        }
    }
}

mod test {

    #[test]
    fn identity_e1_nullary() {
        use super::E1;
        use crate::category::HasIdentity;
        use crate::operadic::Operadic;
        use crate::{assert_err, assert_ok};

        let mut x = E1::identity(&());
        let zero_ary = E1::new(vec![], true);
        let composed = x.operadic_substitution(0, zero_ary);
        assert_ok!(composed);
        assert_eq!(x.arity, 0);
        assert_eq!(x.sub_intervals, vec![]);

        let mut x = E1::identity(&());
        let zero_ary = E1::new(vec![], true);
        let composed = x.operadic_substitution(1, zero_ary);
        assert_err!(composed);

        let id = E1::identity(&());
        let mut x = E1::new(vec![], true);
        let composed = x.operadic_substitution(0, id);
        assert_eq!(
            composed,
            Err("There aren't enough inputs to graft onto the 1'th one".into())
        );
        let id = E1::identity(&());
        let composed = x.operadic_substitution(5, id);
        assert_eq!(
            composed,
            Err("There aren't enough inputs to graft onto the 6'th one".into())
        );
    }

    #[test]
    fn identity_e1_random() {
        use super::{IntervalCoord, E1};
        use crate::assert_ok;
        use crate::category::HasIdentity;
        use crate::operadic::Operadic;
        use rand::Rng;

        let arity_max: u8 = 20;
        let mut rng = rand::thread_rng();
        let trial_num = 10;

        for _ in 0..trial_num {
            let used_arity: u8 = rng.gen_range(1..arity_max);
            let mut sub_ints: Vec<IntervalCoord> = (0..2 * used_arity)
                .map(|_| rng.gen_range(0.0..1.0))
                .collect();
            sub_ints.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
            let sub_intervals: Vec<(IntervalCoord, IntervalCoord)> = sub_ints
                .chunks_exact(2)
                .map(|chunk| (chunk[0], chunk[1]))
                .collect();
            let mut as_e1_v1 = E1::new(sub_intervals.clone(), false);
            let as_e1_v2 = E1::new(sub_intervals.clone(), false);
            let which_to_replace = rng.gen_range(0..used_arity);
            let id = E1::identity(&());
            let composed = as_e1_v1.operadic_substitution(which_to_replace as usize, id);
            assert_ok!(composed);
            assert_eq!(as_e1_v1.arity, used_arity as usize);
            assert_eq!(as_e1_v1.sub_intervals, sub_intervals);
            let mut id = E1::identity(&());
            let composed = id.operadic_substitution(0, as_e1_v2);
            assert_ok!(composed);
            assert_eq!(id.arity, used_arity as usize);
            assert_eq!(id.sub_intervals, sub_intervals);
        }
    }

    #[test]
    fn two_random_nontrivials() {
        use super::{IntervalCoord, E1};
        use crate::assert_ok;
        use crate::operadic::Operadic;
        use rand::Rng;

        let arity_max: u8 = 20;
        let mut rng = rand::thread_rng();
        let trial_num = 10;

        for _ in 0..trial_num {
            let used_arity_1: u8 = rng.gen_range(1..arity_max);
            let mut sub_ints: Vec<IntervalCoord> = (0..2 * used_arity_1)
                .map(|_| rng.gen_range(0.0..1.0))
                .collect();
            sub_ints.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
            let sub_intervals: Vec<(IntervalCoord, IntervalCoord)> = sub_ints
                .chunks_exact(2)
                .map(|chunk| (chunk[0], chunk[1]))
                .collect();
            let as_e1_v1 = E1::new(sub_intervals.clone(), false);

            let used_arity_2: u8 = rng.gen_range(1..arity_max);
            let mut sub_ints: Vec<IntervalCoord> = (0..2 * used_arity_2)
                .map(|_| rng.gen_range(0.0..1.0))
                .collect();
            sub_ints.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
            let sub_intervals: Vec<(IntervalCoord, IntervalCoord)> = sub_ints
                .chunks_exact(2)
                .map(|chunk| (chunk[0], chunk[1]))
                .collect();
            let mut as_e1_v2 = E1::new(sub_intervals.clone(), false);

            let which_to_replace = rng.gen_range(0..used_arity_2);

            let split_box = as_e1_v2.sub_intervals[which_to_replace as usize];

            let composed = as_e1_v2.operadic_substitution(which_to_replace as usize, as_e1_v1);
            assert_ok!(composed);
            assert_eq!(as_e1_v2.arity, (used_arity_1 + used_arity_2 - 1) as usize);
            for (which, interval) in sub_intervals.iter().enumerate() {
                if which == (which_to_replace as usize) {
                    assert!(!as_e1_v2.sub_intervals.contains(interval));
                } else {
                    assert!(as_e1_v2.sub_intervals.contains(interval));
                }
            }
            let res = as_e1_v2.coalesce_boxes(split_box);
            assert_ok!(res);
            assert_eq!(as_e1_v2.arity, used_arity_2 as usize);
            for interval in &sub_intervals {
                assert!(as_e1_v2.sub_intervals.contains(interval));
            }
        }
    }
}
