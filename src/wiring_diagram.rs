use crate::named_cospan::NamedCospan;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[allow(dead_code)]
enum InOut {
    In,
    Out,
}

#[allow(dead_code)]
struct WiringDiagram<Lambda: Eq + Copy, InterCircle: Eq, IntraCircle: Eq + Ord>(
    NamedCospan<Lambda, (InOut, InterCircle, IntraCircle), (InOut, IntraCircle)>,
);

impl<'a, Lambda, InterCircle, IntraCircle> WiringDiagram<Lambda, InterCircle, IntraCircle>
where
    Lambda: Eq + Copy,
    InterCircle: Eq,
    IntraCircle: Eq + Ord,
{
    #[allow(dead_code)]
    fn operadic_substitution(&mut self, which_circle: InterCircle, _other: Self)
    where
        InterCircle: Copy,
        IntraCircle: Copy,
    {
        let pred_left = |z: (InOut, InterCircle, IntraCircle)| z.1 == which_circle;
        let pred_right = |_| false;
        let _found_nodes = NamedCospan::<
            Lambda,
            (InOut, InterCircle, IntraCircle),
            (InOut, IntraCircle),
        >::find_nodes_by_name_predicate(
            &self.0, pred_left, pred_right, false
        );
        todo!()
    }
}
