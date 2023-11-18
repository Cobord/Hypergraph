use either::Either::{Left, Right};

use crate::operadic::{Operadic, OperadicError};

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

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub enum Dir {
    In,
    Out,
    Undirected,
}

impl Dir {
    pub fn flipped(self) -> Self {
        match self {
            Self::In => Self::Out,
            Self::Out => Self::In,
            Self::Undirected => Self::Undirected,
        }
    }
}

type Pair<T> = (T, T);
type EitherPair<T, U> = Either<Pair<T>, Pair<U>>;

/*
a wiring diagram with wires labelled using Lambda
is a cospan between sets A and B
A describes a set of nodes on internal circles each one being labelled with
    an Dir for orientation
    an InterCircle for which of multiple internal circles we are on
    an IntraCircle to label which node on that circle it is
B describes a set of nodes on the single external circle
    an Dir for orientation
    an IntraCircle to label which node on that circle it is
*/
#[derive(Clone)]
#[repr(transparent)]
pub struct WiringDiagram<
    Lambda: Eq + Copy + Debug,
    InterCircle: Eq + Clone,
    IntraCircle: Eq + Clone,
>(NamedCospan<Lambda, (Dir, InterCircle, IntraCircle), (Dir, IntraCircle)>);

impl<Lambda, InterCircle, IntraCircle> WiringDiagram<Lambda, InterCircle, IntraCircle>
where
    Lambda: Eq + Copy + Debug,
    InterCircle: Eq + Clone,
    IntraCircle: Eq + Clone,
{
    pub fn new(
        inside: NamedCospan<Lambda, (Dir, InterCircle, IntraCircle), (Dir, IntraCircle)>,
    ) -> Self {
        Self(inside)
    }

    #[allow(dead_code)]
    pub fn change_boundary_node_name(
        &mut self,
        name_pair: EitherPair<(Dir, InterCircle, IntraCircle), (Dir, IntraCircle)>,
    ) {
        /*
        change a name of a boundary node
        specific to LeftPortName and RightPortName of WiringDiagram being in the specific format
            with Dir,InterCircle and IntraCircle
        gives warning and makes no change when there is no node with the desired name
        */
        self.0.change_boundary_node_name(name_pair);
    }

    #[allow(dead_code)]
    pub fn toggle_orientation(&mut self, of_left_side: bool) {
        let toggler = if of_left_side {
            Left(|z: &mut (Dir, InterCircle, IntraCircle)| {
                z.0 = z.0.flipped();
            })
        } else {
            Right(|z: &mut (Dir, IntraCircle)| {
                z.0 = z.0.flipped();
            })
        };
        self.0.change_boundary_node_names(toggler);
    }

    #[allow(dead_code)]
    pub fn add_boundary_node_unconnected(
        &mut self,
        type_: Lambda,
        new_name: Either<(Dir, InterCircle, IntraCircle), (Dir, IntraCircle)>,
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
        node_1: Either<(Dir, InterCircle, IntraCircle), (Dir, IntraCircle)>,
        node_2: Either<(Dir, InterCircle, IntraCircle), (Dir, IntraCircle)>,
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
        which_node: Either<(Dir, InterCircle, IntraCircle), (Dir, IntraCircle)>,
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
}

impl<Lambda, InterCircle, IntraCircle> Operadic<InterCircle>
    for WiringDiagram<Lambda, InterCircle, IntraCircle>
where
    Lambda: Eq + Copy + Debug,
    InterCircle: Eq + Copy,
    IntraCircle: Eq + Copy,
{
    fn operadic_substitution(
        &mut self,
        which_circle: InterCircle,
        mut internal_other: Self,
    ) -> Result<(), OperadicError> {
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

        /*
        identity on all the other internal circles
        the names are orientation reversed for the identity
        if we draw a line connecting the endpoints on internal and external circles
        the one on the internal circle pointing into the boundary
            means the one on the external circle points away from the boundary
        and vice versa
        */
        internal_other.0.monoidal(NamedCospan::identity(
            &self_inner_interface_unaffected,
            &self_inner_names_unaffected,
            |left_name| (left_name, (left_name.0.flipped(), left_name.2)),
        ));

        /*
        permute the codomain of internal so it lines up with the domain of self
        by name
        the composition only has a trouble if the types don't match up
        it ignores the names on the internal junction
        so if we want to glue by node name, we must permute first
        the orientations flip so that across the internal junction all lines
        have consistent orientation upon gluing
        */
        let p = necessary_permutation(
            internal_other.0.right_names(),
            &self
                .0
                .left_names()
                .iter()
                .map(|z| (z.0.flipped(), z.2))
                .collect::<Vec<_>>(),
        )?;
        internal_other.0.permute_side(&p, true);

        self.0 = internal_other
            .0
            .compose(&self.0)
            .map_err(|z| format!("{:?}", z))?;
        Ok(())
    }
}

mod test {

    #[test]
    fn no_input_example() {
        use super::{Dir, WiringDiagram};
        use crate::named_cospan::NamedCospan;
        use either::Right;
        let unchanged_right_names = vec![
            (Dir::In, 0),
            (Dir::Out, 1),
            (Dir::In, 2),
            (Dir::Out, 3),
            (Dir::Out, 4),
        ];
        let mut example: WiringDiagram<_, (), _> = WiringDiagram::new(NamedCospan::new(
            vec![],
            vec![0, 1, 2, 2, 0],
            vec![true, true, false],
            vec![],
            unchanged_right_names.clone(),
        ));
        assert_eq!(*example.0.right_names(), unchanged_right_names);
        example.change_boundary_node_name(Right(((Dir::In, 0), (Dir::Out, 0))));
        let changed_names = example.0.right_names();
        assert_eq!(changed_names[0], (Dir::Out, 0));
        assert_eq!(changed_names[1..], unchanged_right_names[1..]);
    }

    #[test]
    fn operadic() {
        use super::{Dir, WiringDiagram};
        use crate::assert_ok;
        use crate::category::Composable;
        use crate::named_cospan::NamedCospan;
        use crate::operadic::Operadic;
        use crate::symmetric_monoidal::SymmetricMonoidalMorphism;
        use permutations::Permutation;

        type WireName = usize;
        type CircleName = i32;
        let inner_right_names: Vec<(_, WireName)> = vec![
            (Dir::In, 0),
            (Dir::Out, 1),
            (Dir::In, 2),
            (Dir::Out, 3),
            (Dir::Out, 4),
        ];
        let mut outer_left_names: Vec<(_, CircleName, _)> = inner_right_names
            .iter()
            .map(|(orient, name)| (orient.flipped(), 0, *name))
            .collect();
        outer_left_names.push((Dir::Undirected, 1, 500));

        /*
        inner circle has no further inner circles
        it has 5 ports on the outside
        0 and 4 are connected to a common middle with type true
        2 and 3 are connected to a common middle with type false
        1 is connected to a middle with type true
        0 and 2 are oriented in to the boundary
        their names are just the numbers and orientations
        */
        let example_inner: WiringDiagram<_, CircleName, WireName> =
            WiringDiagram::new(NamedCospan::new(
                vec![],
                vec![0, 1, 2, 2, 0],
                vec![true, true, false],
                vec![],
                inner_right_names,
            ));
        /*
        outer circle has 2 inner circles
        the first has 5 ports for the outer of previous to connect to
        0, 1 and 4 are connected to a common middle with type true
            and that is connected to the only port on the very outer circle
        2 and 3 are connected to a common middle with type false
        the second has 1 port which is undirected and labelled 500 and of type false
        */
        let mut example_outer: WiringDiagram<_, _, _> = WiringDiagram::new(NamedCospan::new(
            vec![0, 0, 1, 1, 0, 1],
            vec![0],
            vec![true, false],
            outer_left_names.clone(),
            vec![(Dir::Out, 0)],
        ));
        /*
        permuting the domain of outer doesn't matter because the
        wires will be matched up by name not by index
        */
        use rand::seq::SliceRandom;
        use rand::thread_rng;
        let mut rng = thread_rng();
        let mut y: Vec<usize> = (0..6).collect();
        y.shuffle(&mut rng);
        let p = Permutation::try_from(&y).unwrap();
        example_outer.0.permute_side(&p, false);
        example_outer.0.assert_valid_nohash(false);
        assert_eq!(*example_outer.0.left_names(), p.permute(&outer_left_names));
        assert_eq!(*example_outer.0.right_names(), vec![(Dir::Out, 0)]);
        assert_eq!(
            example_outer.0.domain(),
            p.permute(&vec![true, true, false, false, true, false])
        );
        assert_eq!(*example_outer.0.codomain(), vec![true]);

        let op_subbed = example_outer.operadic_substitution(0, example_inner);
        assert_ok!(op_subbed);
        example_outer.0.assert_valid_nohash(false);
        assert_eq!(
            *example_outer.0.left_names(),
            vec![(Dir::Undirected, 1, 500)]
        );
        assert_eq!(*example_outer.0.domain(), vec![false]);
        assert_eq!(*example_outer.0.right_names(), vec![(Dir::Out, 0)]);
        assert_eq!(*example_outer.0.codomain(), vec![true]);
    }

    #[test]
    fn operadic_multiple() {
        use super::{Dir, WiringDiagram};
        use crate::assert_err;
        use crate::assert_ok;
        use crate::category::Composable;
        use crate::named_cospan::NamedCospan;
        use crate::operadic::Operadic;
        use crate::symmetric_monoidal::SymmetricMonoidalMorphism;
        use either::Either::{Left, Right};
        use permutations::Permutation;

        type WireName = char;
        type CircleName = i32;

        let outer_label = |c: WireName| (Dir::Undirected, c);
        let outer_right_names: Vec<(_, WireName)> = ['a', 'b', 'c', 'd', 'e']
            .into_iter()
            .map(outer_label)
            .collect();

        let inner_label = |(w, c): (WireName, CircleName)| (Dir::Undirected, c, w);
        let outer_left_names: Vec<(_, CircleName, WireName)> = [
            ('r', 1),
            ('s', 1),
            ('t', 1),
            ('u', 2),
            ('v', 2),
            ('w', 3),
            ('x', 3),
            ('y', 3),
            ('z', 3),
        ]
        .into_iter()
        .map(inner_label)
        .collect();

        /*
        outer circle has 3 inner circles
        the first has 3 ports
            they are named r,s,t and connected to 2,1,3 in the middle
        the second has 2 ports
            they are named u,v and are connected to 4 and 3
        the third has 3 ports
            they are named w,x,y,z and are connected to 1,4,5,6
        there are no colors to the wires
        */
        let mut example_outer: WiringDiagram<_, _, _> = WiringDiagram::new(NamedCospan::new(
            vec![1, 0, 2, 3, 2, 0, 3, 4, 5],
            vec![0, 1, 2, 4, 5],
            vec![(); 6],
            outer_left_names.clone(),
            outer_right_names.clone(),
        ));
        /*
        permuting the domain of outer doesn't matter because the
        wires will be matched up by name not by index
        */
        use rand::seq::SliceRandom;
        use rand::thread_rng;
        let mut rng = thread_rng();
        let mut y: Vec<usize> = (0..9).collect();
        y.shuffle(&mut rng);
        let p1 = Permutation::try_from(&y).unwrap();
        example_outer.0.permute_side(&p1, false);
        example_outer.0.assert_valid_nohash(false);

        let mut y: Vec<usize> = (0..5).collect();
        y.shuffle(&mut rng);
        let p2 = Permutation::try_from(&y).unwrap();
        example_outer.0.permute_side(&p2, true);
        example_outer.0.assert_valid_nohash(false);

        assert_eq!(*example_outer.0.left_names(), p1.permute(&outer_left_names));
        assert_eq!(
            *example_outer.0.right_names(),
            p2.permute(&outer_right_names)
        );
        assert_eq!(example_outer.0.domain(), vec![(); 9]);
        assert_eq!(example_outer.0.codomain(), vec![(); 5]);

        let inner_1_right_names: Vec<(_, WireName)> = outer_left_names
            .iter()
            .filter_map(|(in_out, circle_name, wire_name)| {
                if *circle_name == 1 {
                    Some((in_out.flipped(), *wire_name))
                } else {
                    None
                }
            })
            .collect();
        let inner_1_left_names: Vec<(Dir, CircleName, WireName)> = vec![];

        /*
        first inner circle gets substituted for the r,s,t circle
        t goes to a unconnected middle
        r and s go to the same middle
        there are no internal circles
        */
        let example_inner_1: WiringDiagram<_, _, _> = WiringDiagram::new(NamedCospan::new(
            vec![],
            vec![1, 1, 0],
            vec![(), ()],
            inner_1_left_names,
            inner_1_right_names,
        ));

        let subbed = example_outer.operadic_substitution(1, example_inner_1);
        assert_ok!(subbed);

        example_outer.0.assert_valid_nohash(false);
        let expected_left_names = [
            (Dir::Undirected, 2, 'u'),
            (Dir::Undirected, 2, 'v'),
            (Dir::Undirected, 3, 'w'),
            (Dir::Undirected, 3, 'x'),
            (Dir::Undirected, 3, 'y'),
            (Dir::Undirected, 3, 'z'),
        ];
        let mut obs_left_names = example_outer.0.left_names().clone();
        obs_left_names.sort();
        assert_eq!(obs_left_names, expected_left_names.to_vec());
        assert_eq!(*example_outer.0.domain(), vec![(); 9 - 3]);
        let expected_right_names = [
            (Dir::Undirected, 'a'),
            (Dir::Undirected, 'b'),
            (Dir::Undirected, 'c'),
            (Dir::Undirected, 'd'),
            (Dir::Undirected, 'e'),
        ];
        let mut obs_right_names = example_outer.0.right_names().clone();
        obs_right_names.sort();
        assert_eq!(obs_right_names, expected_right_names.to_vec());
        assert_eq!(*example_outer.0.codomain(), vec![(); 5]);

        assert!(example_outer
            .0
            .map_to_same(Right(outer_label('a')), Right(outer_label('b'))));
        assert!(example_outer
            .0
            .map_to_same(Right(outer_label('a')), Left(inner_label(('w', 3)))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('a')), Right(outer_label('c'))));
        assert!(example_outer
            .0
            .map_to_same(Right(outer_label('c')), Left(inner_label(('v', 2)))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('a')), Right(outer_label('d'))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('a')), Right(outer_label('e'))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('c')), Right(outer_label('d'))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('c')), Right(outer_label('e'))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('d')), Right(outer_label('e'))));
        assert!(example_outer
            .0
            .map_to_same(Right(outer_label('d')), Left(inner_label(('y', 3)))));
        assert!(example_outer
            .0
            .map_to_same(Right(outer_label('e')), Left(inner_label(('z', 3)))));
        assert!(example_outer
            .0
            .map_to_same(Left(inner_label(('u', 2))), Left(inner_label(('x', 3)))));
        assert!(!example_outer
            .0
            .map_to_same(Left(inner_label(('u', 2))), Right(outer_label('b'))));
        assert!(!example_outer
            .0
            .map_to_same(Left(inner_label(('u', 2))), Right(outer_label('c'))));
        assert!(!example_outer
            .0
            .map_to_same(Left(inner_label(('u', 2))), Right(outer_label('d'))));
        assert!(!example_outer
            .0
            .map_to_same(Left(inner_label(('u', 2))), Right(outer_label('e'))));

        let inner_2_right_names: Vec<_> = outer_left_names
            .iter()
            .filter_map(|(in_out, circle_name, wire_name)| {
                if *circle_name == 2 {
                    Some((in_out.flipped(), *wire_name))
                } else {
                    None
                }
            })
            .collect();
        let inner_2_left_names = vec![inner_label(('q', 4))];

        /*
        first inner circle gets substituted for the u,v circle
        u and v go to the same middle
        that middle connects to a inner circle with port name q
        */
        let make_example_inner_2 = || {
            WiringDiagram::new(NamedCospan::new(
                vec![0],
                vec![0, 0],
                vec![()],
                inner_2_left_names.clone(),
                inner_2_right_names.clone(),
            ))
        };

        let subbed = example_outer.operadic_substitution(1, make_example_inner_2());
        assert_err!(subbed);
        let subbed = example_outer.operadic_substitution(3, make_example_inner_2());
        assert_err!(subbed);
        let subbed = example_outer.operadic_substitution(5, make_example_inner_2());
        assert_err!(subbed);
        let subbed = example_outer.operadic_substitution(2, make_example_inner_2());
        assert_ok!(subbed);

        example_outer.0.assert_valid_nohash(false);
        let expected_left_names = [
            (Dir::Undirected, 3, 'w'),
            (Dir::Undirected, 3, 'x'),
            (Dir::Undirected, 3, 'y'),
            (Dir::Undirected, 3, 'z'),
            (Dir::Undirected, 4, 'q'),
        ];
        let mut obs_left_names = example_outer.0.left_names().clone();
        obs_left_names.sort();
        assert_eq!(obs_left_names, expected_left_names.to_vec());
        assert_eq!(*example_outer.0.domain(), vec![(); 9 - 3 - 2 + 1]);
        let expected_right_names = [
            (Dir::Undirected, 'a'),
            (Dir::Undirected, 'b'),
            (Dir::Undirected, 'c'),
            (Dir::Undirected, 'd'),
            (Dir::Undirected, 'e'),
        ];
        let mut obs_right_names = example_outer.0.right_names().clone();
        obs_right_names.sort();
        assert_eq!(obs_right_names, expected_right_names.to_vec());
        assert_eq!(*example_outer.0.codomain(), vec![(); 5]);

        assert!(example_outer
            .0
            .map_to_same(Right(outer_label('a')), Right(outer_label('b'))));
        assert!(example_outer
            .0
            .map_to_same(Right(outer_label('a')), Left(inner_label(('w', 3)))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('a')), Right(outer_label('c'))));
        assert!(example_outer
            .0
            .map_to_same(Right(outer_label('c')), Left(inner_label(('q', 4)))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('a')), Right(outer_label('d'))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('a')), Right(outer_label('e'))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('c')), Right(outer_label('d'))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('c')), Right(outer_label('e'))));
        assert!(!example_outer
            .0
            .map_to_same(Right(outer_label('d')), Right(outer_label('e'))));
        assert!(example_outer
            .0
            .map_to_same(Right(outer_label('d')), Left(inner_label(('y', 3)))));
        assert!(example_outer
            .0
            .map_to_same(Right(outer_label('e')), Left(inner_label(('z', 3)))));
        assert!(example_outer
            .0
            .map_to_same(Left(inner_label(('q', 4))), Left(inner_label(('x', 3)))));
        assert!(!example_outer
            .0
            .map_to_same(Left(inner_label(('q', 4))), Right(outer_label('b'))));
        assert!(example_outer
            .0
            .map_to_same(Left(inner_label(('q', 4))), Right(outer_label('c'))));
        assert!(!example_outer
            .0
            .map_to_same(Left(inner_label(('q', 4))), Right(outer_label('d'))));
        assert!(!example_outer
            .0
            .map_to_same(Left(inner_label(('q', 4))), Right(outer_label('e'))));
    }
}
