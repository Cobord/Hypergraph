use std::fmt::Debug;

use crate::named_cospan::NamedCospan;
use crate::utils::{keep_left, necessary_permutation, remove_multiple};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[allow(dead_code)]
enum InOut {
    In,
    Out,
}

#[allow(dead_code)]
struct WiringDiagram<Lambda: Eq + Copy + Debug, InterCircle: Eq, IntraCircle: Eq>(
    NamedCospan<Lambda, (InOut, InterCircle, IntraCircle), (InOut, IntraCircle)>,
);

impl<'a, Lambda, InterCircle, IntraCircle> WiringDiagram<Lambda, InterCircle, IntraCircle>
where
    Lambda: Eq + Copy + Debug,
    InterCircle: Eq,
    IntraCircle: Eq,
{
    #[allow(dead_code)]
    pub fn operadic_substitution(
        &mut self,
        which_circle: InterCircle,
        mut internal_other: Self,
    ) -> Result<(), String>
    where
        InterCircle: Copy,
        IntraCircle: Copy,
    {
        let pred_left = |z: (InOut, InterCircle, IntraCircle)| z.1 == which_circle;
        let found_nodes: Vec<usize> = NamedCospan::<
            Lambda,
            (InOut, InterCircle, IntraCircle),
            (InOut, IntraCircle),
        >::find_nodes_by_name_predicate(
            &self.0, pred_left, |_| false, false
        )
        .iter()
        .filter_map(keep_left)
        .collect();

        let mut self_inner_interface_unaffected = self.0.left_interface();
        remove_multiple(&mut self_inner_interface_unaffected, found_nodes.clone());
        let mut self_inner_names_unaffected = self.0.left_names().clone();
        remove_multiple(&mut self_inner_names_unaffected, found_nodes);
        let left_name_to_both_names =
            |left_name: (InOut, InterCircle, IntraCircle)| (left_name, (left_name.0, left_name.2));
        let cur_identity = NamedCospan::identity(
            &self_inner_interface_unaffected,
            &self_inner_names_unaffected,
            left_name_to_both_names,
        );
        internal_other.0.monoidal(cur_identity);

        let p = necessary_permutation(
            internal_other.0.right_names(),
            &self
                .0
                .left_names()
                .iter()
                .map(|z| (z.0, z.2))
                .collect::<Vec<(InOut, IntraCircle)>>(),
        )?;

        internal_other.0.permute_leg(&p, true);
        self.0 = self.0.compose(internal_other.0)?;
        Ok(())
    }
}
