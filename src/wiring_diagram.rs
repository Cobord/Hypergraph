use {
    crate::{
        category::Composable,
        monoidal::Monoidal,
        named_cospan::NamedCospan,
        symmetric_monoidal::SymmetricMonoidalMorphism,
        utils::{necessary_permutation, remove_multiple},
    },
    either::Either,
    std::fmt::Debug,
};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[allow(dead_code)]
pub enum InOut {
    In,
    Out,
    Undirected,
}

impl InOut {
    #[allow(dead_code)]
    pub fn flipped(self) -> Self {
        match self {
            Self::In => Self::Out,
            Self::Out => Self::In,
            Self::Undirected => Self::Undirected,
        }
    }
}

type Doubled<T> = (T, T);
type DoubledEither<T, U> = Either<Doubled<T>, Doubled<U>>;

/*
a wiring diagram with wires labelled using Lambda
is a cospan between sets A and B
A describes a set of nodes on internal circles each one being labelled with
    an InOut for orientation
    an InterCircle for which of multiple internal circles we are on
    an IntraCircle to label which node on that circle it is
B describes a set of nodes on the single external circle
    an InOut for orientation
    an IntraCircle to label which node on that circle it is
*/
#[allow(dead_code)]
#[repr(transparent)]
pub struct WiringDiagram<
    Lambda: Eq + Copy + Debug,
    InterCircle: Eq + Clone,
    IntraCircle: Eq + Clone,
>(NamedCospan<Lambda, (InOut, InterCircle, IntraCircle), (InOut, IntraCircle)>);

impl<Lambda, InterCircle, IntraCircle> WiringDiagram<Lambda, InterCircle, IntraCircle>
where
    Lambda: Eq + Copy + Debug,
    InterCircle: Eq + Clone,
    IntraCircle: Eq + Clone,
{
    pub fn new(
        inside: NamedCospan<Lambda, (InOut, InterCircle, IntraCircle), (InOut, IntraCircle)>,
    ) -> Self {
        Self(inside)
    }

    #[allow(dead_code)]
    pub fn change_boundary_node_name(
        &mut self,
        name_pair: DoubledEither<(InOut, InterCircle, IntraCircle), (InOut, IntraCircle)>,
    ) {
        /*
        change a name of a boundary node
        specific to LeftPortName and RightPortName of WiringDiagram being in the specific format
            with InOut,InterCircle and IntraCircle
        gives warning and makes no change when there is no node with the desired name
        */
        self.0.change_boundary_node_name(name_pair);
    }

    #[allow(dead_code)]
    pub fn add_boundary_node_unconnected(
        &mut self,
        type_: Lambda,
        new_name: Either<(InOut, InterCircle, IntraCircle), (InOut, IntraCircle)>,
    ) {
        /*
        add a new boundary node that maps to a new middle node of specified label type_
        name it according to new_name
        which side depends on whether new_name is Left/Right
        that new middle node connects to nothing else, so this new node is unconnected to the
            rest of the diagram
        */
        let _ = self.0.add_boundary_node_unknown_target(type_, new_name);
    }

    #[allow(dead_code)]
    pub fn connect_pair(
        &mut self,
        node_1: Either<(InOut, InterCircle, IntraCircle), (InOut, IntraCircle)>,
        node_2: Either<(InOut, InterCircle, IntraCircle), (InOut, IntraCircle)>,
    ) {
        /*
        first find node_1 and node_2 by their names
        if nodes with those names do not exist, then make no change
        collapse the middle nodes that node_1 and node_2 connect to (A and B)
        into a single middle node with the same label as the shared label
        of A and B
        if A and B do not have the same label, give a warning and make no change
        */
        self.0.connect_pair(node_1, node_2)
    }

    #[allow(dead_code)]
    pub fn delete_boundary_node(
        &mut self,
        which_node: Either<(InOut, InterCircle, IntraCircle), (InOut, IntraCircle)>,
    ) {
        /*
        find a node by it's name
        if it is not found, there is nothing to delet so give a warning and no change made
        if it is found, delete that node (see delete_boundary_node in NamedCospan and the CAUTION therein)
        */
        self.0.delete_boundary_node_by_name(which_node)
    }

    #[allow(dead_code)]
    pub fn map<F, Mu>(&self, f: F) -> WiringDiagram<Mu, InterCircle, IntraCircle>
    where
        F: Fn(Lambda) -> Mu,
        Mu: Sized + Eq + Copy + Debug,
    {
        /*
        change the labels with the function f
        */
        WiringDiagram::new(self.0.map(f))
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
        /*
        replace the internal circle of self labelled by which_circle (call it C)
        with the contents of internal_other
        so that the external circle of internal_other is interpreted as C
        the new internal circles of self are all the old internal circles except for C
            and all the internal circles of internal_other
        */
        let found_nodes: Vec<_> = NamedCospan::find_nodes_by_name_predicate(
            &self.0,
            |z| z.1 == which_circle,
            |_| false,
            false,
        )
        .iter()
        .filter_map(|x| x.left())
        .collect();

        let mut self_inner_interface_unaffected = self.0.domain();
        remove_multiple(&mut self_inner_interface_unaffected, found_nodes.clone());
        let mut self_inner_names_unaffected = self.0.left_names().clone();
        remove_multiple(&mut self_inner_names_unaffected, found_nodes);

        // todo handle orientations

        internal_other.0.monoidal(NamedCospan::identity(
            &self_inner_interface_unaffected,
            &self_inner_names_unaffected,
            |left_name| (left_name, (left_name.0, left_name.2)),
        ));

        let p = necessary_permutation(
            internal_other.0.right_names(),
            &self
                .0
                .left_names()
                .iter()
                .map(|z| (z.0, z.2))
                .collect::<Vec<_>>(),
        )?;

        internal_other.0.permute_side(&p, true);
        self.0 = self.0.compose(&internal_other.0)?;
        Ok(())
    }
}

mod test {

    #[test]
    fn no_input_example() {
        use super::{InOut, WiringDiagram};
        use crate::named_cospan::NamedCospan;
        use either::Right;
        let unchanged_right_names = vec![
            (InOut::In, 0),
            (InOut::Out, 1),
            (InOut::In, 2),
            (InOut::Out, 3),
            (InOut::Out, 4),
        ];
        let mut example: WiringDiagram<_, (), _> = WiringDiagram::new(NamedCospan::new(
            vec![],
            vec![0, 1, 2, 2, 0],
            vec![true, true, false],
            vec![],
            unchanged_right_names.clone(),
        ));
        assert_eq!(*example.0.right_names(), unchanged_right_names);
        example.change_boundary_node_name(Right(((InOut::In, 0), (InOut::Out, 0))));
        let changed_names = example.0.right_names();
        assert_eq!(changed_names[0], (InOut::Out, 0));
        assert_eq!(changed_names[1..], unchanged_right_names[1..]);
    }
}
