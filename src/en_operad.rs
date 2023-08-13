use itertools::Itertools;

use crate::{category::HasIdentity, operadic::Operadic};

#[allow(dead_code)]
struct E1 {
    arity: usize,
    sub_intervals: Vec<(f32, f32)>,
}

impl E1 {
    #[allow(dead_code)]
    fn new(sub_intervals: Vec<(f32, f32)>) -> Self {
        /*
        new n-ary operation in E1 operad where n is the length of
        */
        for (a, b) in &sub_intervals {
            assert!(
                *a < *b && 0.0 <= *a && *b <= 1.0,
                "Each subinterval must be an interval contained in (0,1)"
            );
        }
        for cur_pair in sub_intervals.iter().combinations(2) {
            let (a, b) = cur_pair[0];
            let (c, d) = cur_pair[1];
            assert!(*b < *c || *d < *a, "The subintervals cannot overlap");
        }
        Self {
            arity: sub_intervals.len(),
            sub_intervals,
        }
    }
}

impl Operadic<usize> for E1 {
    fn operadic_substitution(&mut self, which_input: usize, other_obj: Self) -> Result<(), String> {
        if which_input >= self.arity {
            return Err(format!(
                "There aren't enough inputs to graft onto the {}'th one",
                which_input + 1
            ));
        }
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
    fn identity(_: &()) -> Self {
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
        let zero_ary = E1::new(vec![]);
        let composed = x.operadic_substitution(0, zero_ary);
        assert_ok!(composed);
        assert_eq!(x.arity, 0);
        assert_eq!(x.sub_intervals, vec![]);

        let mut x = E1::identity(&());
        let zero_ary = E1::new(vec![]);
        let composed = x.operadic_substitution(1, zero_ary);
        assert_err!(composed);

        let id = E1::identity(&());
        let mut x = E1::new(vec![]);
        let composed = x.operadic_substitution(0, id);
        assert_eq!(
            composed,
            Err("There aren't enough inputs to graft onto the 1'th one".to_string())
        );
        let id = E1::identity(&());
        let composed = x.operadic_substitution(5, id);
        assert_eq!(
            composed,
            Err("There aren't enough inputs to graft onto the 6'th one".to_string())
        );
    }

    #[test]
    fn identity_e1_random() {
        use super::E1;
        use crate::assert_ok;
        use crate::category::HasIdentity;
        use crate::operadic::Operadic;
        use rand::Rng;

        let arity_max: u8 = 20;
        let mut rng = rand::thread_rng();
        let trial_num = 10;

        for _ in 0..trial_num {
            let used_arity: u8 = rng.gen_range(1..arity_max);
            let mut sub_ints: Vec<f32> = (0..2 * used_arity)
                .map(|_| rng.gen_range(0.0..1.0))
                .collect();
            sub_ints.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
            let sub_intervals: Vec<(f32, f32)> = sub_ints
                .chunks_exact(2)
                .map(|chunk| (chunk[0], chunk[1]))
                .collect();
            let mut as_e1_v1 = E1::new(sub_intervals.clone());
            let as_e1_v2 = E1::new(sub_intervals.clone());
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
}
