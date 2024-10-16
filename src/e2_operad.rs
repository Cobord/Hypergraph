use itertools::Itertools;
use num::pow;
use std::collections::HashSet;

use crate::{
    category::HasIdentity,
    e1_operad::E1,
    operadic::{Operadic, OperadicError},
};

type PointCenter = (f32, f32);
type Radius = f32;
type CoalesceError = String;

fn disk_contains(
    c: PointCenter,
    r: Radius,
    query_center: PointCenter,
    query_radius: Option<Radius>,
) -> bool {
    let displace: PointCenter = (c.0 - query_center.0, c.1 - query_center.1);
    let center_contained = displace.0 * displace.0 + displace.1 * displace.1 <= r * r;
    if center_contained {
        if let Some(real_rad) = query_radius {
            let dist_c_qc_squared = pow(c.0 - query_center.0, 2) + pow(c.1 - query_center.1, 2);
            let dist_c_qc = dist_c_qc_squared.sqrt();
            dist_c_qc + real_rad <= r
        } else {
            // D(c,r) contains the point query_center
            true
        }
    } else {
        false
    }
}

fn disk_closeness(a: PointCenter, b: Radius, c: PointCenter, d: Radius) -> Radius {
    let dist_a_c_squared = pow(c.0 - a.0, 2) + pow(c.1 - a.1, 2);
    let dist_a_c = dist_a_c_squared.sqrt();
    dist_a_c - (b + d)
}

fn disk_overlaps(a: PointCenter, b: Radius, c: PointCenter, d: Radius) -> bool {
    disk_closeness(a, b, c, d).is_sign_negative()
}

#[allow(dead_code)]
pub struct E2<Name> {
    arity: usize,
    sub_circles: Vec<(Name, PointCenter, Radius)>,
}

impl<Name> E2<Name>
where
    Name: Eq + std::hash::Hash + Clone + std::fmt::Debug,
{
    #[allow(dead_code)]
    pub fn new(sub_circles: Vec<(Name, PointCenter, Radius)>, overlap_check: bool) -> Self {
        /*
        new n-ary operation in E2 operad where n is the length of input
        */
        for (_a, b, c) in &sub_circles {
            assert!(
                disk_contains((0.0, 0.0), 1.0, *b, Some(*c)),
                "Each subcircle must be contained in the unit disk"
            );
        }
        assert!(
            sub_circles.iter().map(|(a, _, _)| a).all_unique(),
            "each subcircle must have a unique name"
        );
        if overlap_check {
            for d_pair in sub_circles.iter().combinations(2) {
                let d1 = d_pair[0];
                let d2 = d_pair[1];
                assert!(
                    !disk_overlaps(d1.1, d1.2, d2.1, d2.2),
                    "The input circles cannot overlap"
                );
            }
        }
        Self {
            arity: sub_circles.len(),
            sub_circles,
        }
    }

    #[allow(dead_code)]
    pub fn coalesce_boxes(
        &mut self,
        all_in_this_circle: (Name, PointCenter, Radius),
    ) -> Result<(), CoalesceError> {
        self.can_coalesce_boxes((all_in_this_circle.1, all_in_this_circle.2))?;
        let (a, b, c) = all_in_this_circle;
        self.sub_circles
            .retain(|(_, d, _)| !disk_contains(b, c, *d, None));
        self.sub_circles.push((a, b, c));
        self.arity = self.sub_circles.len();
        Ok(())
    }

    pub fn can_coalesce_boxes(
        &self,
        all_in_this_disk: (PointCenter, Radius),
    ) -> Result<(), CoalesceError> {
        let (a, b) = all_in_this_disk;
        if disk_contains((0.0, 0.0), 1.0, a, Some(b)) {
            return Err("The coalescing disk must be contained in the unit disk".to_string());
        }
        for cur_pair in &self.sub_circles {
            let (_, c, d) = cur_pair;
            let contained_within = disk_contains(a, b, *c, Some(*d));
            let disjoint_from = !disk_overlaps(a, b, *c, *d);
            let bad_config = !(contained_within || disjoint_from);
            if bad_config {
                return Err("All subcircles must be either contained within or disjoint from the coalescing disk".to_string());
            }
        }
        Ok(())
    }

    #[allow(dead_code)]
    pub fn min_closeness(&self) -> Option<Radius> {
        if self.arity < 2 {
            return None;
        }
        let mut min_seen = 2.0;
        for circle_pair in self.sub_circles.iter().combinations(2) {
            let circ_0 = circle_pair[0];
            let circ_1 = circle_pair[1];
            let cur_dist = disk_closeness(circ_0.1, circ_0.2, circ_1.1, circ_1.2);
            if cur_dist < min_seen {
                min_seen = cur_dist;
            }
        }
        Some(min_seen)
    }

    #[allow(dead_code)]
    pub fn from_e1_config(e1_config: E1, disk_namer: impl Fn(usize) -> Name) -> Self {
        let sub_intervals = e1_config.extract_sub_intervals();
        let sub_circles = sub_intervals.iter().enumerate().map(|(idx, interval)| {
            let new_center = ((interval.1 + interval.0) - 1.0, 0.0);
            let new_radius = interval.1 - interval.0;
            (disk_namer(idx), new_center, new_radius)
        });
        Self {
            arity: sub_circles.len(),
            sub_circles: sub_circles.collect_vec(),
        }
    }

    #[allow(dead_code)]
    pub fn change_names<Name2: Eq + std::hash::Hash + Clone + std::fmt::Debug>(
        self,
        name_changer: impl Fn(Name) -> Name2,
    ) -> E2<Name2> {
        let new_sub_circles = self
            .sub_circles
            .into_iter()
            .map(|old_sub| (name_changer(old_sub.0), old_sub.1, old_sub.2))
            .collect_vec();
        E2::new(new_sub_circles, false)
    }

    #[allow(dead_code)]
    pub fn change_name(&mut self, name_change: (Name, Name)) {
        let idx_change = self.sub_circles.iter().position(|p| p.0 == name_change.0);
        if let Some(real_idx_change) = idx_change {
            assert!(
                self.sub_circles
                    .iter()
                    .all(|(a, _, _)| *a == name_change.0 || *a != name_change.1),
                "each subcircle must have a unique name"
            );
            self.sub_circles[real_idx_change].0 = name_change.1;
        }
    }
}

impl<Name> HasIdentity<Name> for E2<Name>
where
    Name: Eq + std::hash::Hash + Clone + std::fmt::Debug,
{
    fn identity(to_name: &Name) -> Self {
        Self {
            arity: 1,
            sub_circles: vec![(to_name.clone(), (0.0, 0.0), 1.0)],
        }
    }
}

impl<Name> Operadic<Name> for E2<Name>
where
    Name: Eq + std::hash::Hash + Clone + std::fmt::Debug,
{
    fn operadic_substitution(
        &mut self,
        which_input: Name,
        other_obj: Self,
    ) -> Result<(), OperadicError> {
        let idx_of_input = self
            .sub_circles
            .iter()
            .position(|item| item.0 == which_input);
        if let Some(real_idx) = idx_of_input {
            let (_, inserted_center, inserted_radius) = self.sub_circles.swap_remove(real_idx);
            let selfnames: HashSet<Name> = self
                .sub_circles
                .iter()
                .map(|(selfname, _, _)| selfname.clone())
                .collect();
            let not_still_unique = other_obj
                .sub_circles
                .iter()
                .any(|cur| selfnames.contains(&cur.0));
            if not_still_unique {
                return Err("each subcircle must have a unique name".into());
            }
            let new_circles = other_obj.sub_circles.into_iter().map(|cur| {
                let new_center = (
                    cur.1 .0 * inserted_radius + inserted_center.0,
                    cur.1 .1 * inserted_radius + inserted_center.1,
                );
                (cur.0, new_center, cur.2 * inserted_radius)
            });
            self.sub_circles.extend(new_circles);
            self.arity = self.sub_circles.len();
            Ok(())
        } else {
            Err(format!("No such input {which_input:?} found").into())
        }
    }
}

mod test {

    #[test]
    fn identity_e2_nullary() {
        use super::E2;
        use crate::category::HasIdentity;
        use crate::operadic::Operadic;
        use crate::{assert_err, assert_ok};

        let mut x = E2::identity(&0);
        let zero_ary = E2::new(vec![], true);
        let composed = x.operadic_substitution(0, zero_ary);
        assert_ok!(composed);
        assert_eq!(x.arity, 0);
        assert_eq!(x.sub_circles, vec![]);

        let mut x = E2::identity(&0);
        let zero_ary = E2::new(vec![], true);
        let composed = x.operadic_substitution(1, zero_ary);
        assert_err!(composed);

        let id = E2::identity(&0);
        let mut x = E2::new(vec![], true);
        let composed = x.operadic_substitution(0, id);
        assert_eq!(composed, Err("No such input 0 found".into()));
        let id = E2::identity(&0);
        let composed = x.operadic_substitution(5, id);
        assert_eq!(composed, Err("No such input 5 found".into()));
    }
}
