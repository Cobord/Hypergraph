use either::Either;
use std::fmt::Debug;

use crate::named_cospan::NamedCospan;
use crate::utils::{keep_left, necessary_permutation, remove_multiple};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[allow(dead_code)]
enum InOut {
    In,
    Out,
}

type MiddleIndex = usize;
type Doubled<T> = (T, T);
type DoubledEither<T, U> = Either<Doubled<T>, Doubled<U>>;

#[allow(dead_code)]
struct WiringDiagram<Lambda: Eq + Copy + Debug, InterCircle: Eq + Clone, IntraCircle: Eq + Clone>(
    NamedCospan<Lambda, (InOut, InterCircle, IntraCircle), (InOut, IntraCircle)>,
);

impl<'a, Lambda, InterCircle, IntraCircle> WiringDiagram<Lambda, InterCircle, IntraCircle>
where
    Lambda: Eq + Copy + Debug,
    InterCircle: Eq + Clone,
    IntraCircle: Eq + Clone,
{
    #[allow(dead_code)]
    pub fn new(
        left: Vec<MiddleIndex>,
        right: Vec<MiddleIndex>,
        middle: Vec<Lambda>,
        left_names: Vec<(InOut, InterCircle, IntraCircle)>,
        right_names: Vec<(InOut, IntraCircle)>,
    ) -> Self {
        let inside = NamedCospan::new(left, right, middle, left_names, right_names);
        Self { 0: inside }
    }

    #[allow(dead_code)]
    pub fn change_boundary_node_name(
        &mut self,
        name_pair: DoubledEither<(InOut, InterCircle, IntraCircle), (InOut, IntraCircle)>,
    ) {
        self.0.change_boundary_node_name(name_pair);
    }

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

mod test {

    #[test]
    fn no_input_example() {
        use super::{InOut, WiringDiagram};
        use either::Right;
        let unchanged_right_names = vec![
            (InOut::In, 0),
            (InOut::Out, 1),
            (InOut::In, 2),
            (InOut::Out, 3),
            (InOut::Out, 4),
        ];
        let mut example: WiringDiagram<_, (), _> = WiringDiagram::new(
            vec![],
            vec![0, 1, 2, 2, 0],
            vec![true, true, false],
            vec![],
            unchanged_right_names.clone(),
        );
        assert_eq!(*example.0.right_names(), unchanged_right_names);
        example.change_boundary_node_name(Right(((InOut::In, 0), (InOut::Out, 0))));
        let changed_names = example.0.right_names();
        assert_eq!(changed_names[0], (InOut::Out, 0));
        assert_eq!(changed_names[1..], unchanged_right_names[1..]);
    }
}
