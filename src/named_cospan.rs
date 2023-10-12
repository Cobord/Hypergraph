use crate::category::CompositionError;

use {
    crate::{
        category::{Composable, HasIdentity},
        cospan::Cospan,
        monoidal::{Monoidal, MonoidalMorphism},
        symmetric_monoidal::SymmetricMonoidalMorphism,
        utils::in_place_permute,
    },
    either::Either::{self, Left, Right},
    log::warn,
    permutations::Permutation,
    petgraph::{matrix_graph::NodeIndex, prelude::Graph, stable_graph::DefaultIx},
    std::fmt::Debug,
};

type LeftIndex = usize;
type RightIndex = usize;
type MiddleIndex = usize;
type MiddleIndexOrLambda<Lambda> = Either<MiddleIndex, Lambda>;

#[derive(Clone)]
pub struct NamedCospan<Lambda: Sized + Eq + Copy + Debug, LeftPortName, RightPortName> {
    /*
    a cospan of finite sets
    but this time the elements of the domain and codomain have names
    that we can use to query/delete them specifically
    even as the order gets shuffled around
    */
    cospan: Cospan<Lambda>,
    left_names: Vec<LeftPortName>,
    right_names: Vec<RightPortName>,
}

impl<Lambda, LeftPortName, RightPortName> NamedCospan<Lambda, LeftPortName, RightPortName>
where
    Lambda: Sized + Eq + Copy + Debug,
    LeftPortName: Eq,
    RightPortName: Eq,
{
    pub fn assert_valid_nohash(&self, check_id: bool) {
        self.cospan.assert_valid(check_id, true);
        assert_eq!(
            self.cospan.left_to_middle().len(),
            self.left_names.len(),
            "There was a mismatch between the domain size and the list of their names"
        );
        assert_eq!(
            self.cospan.right_to_middle().len(),
            self.right_names.len(),
            "There was a mismatch between the codomain size and the list of their names"
        );
    }
}

impl<Lambda, LeftPortName, RightPortName> NamedCospan<Lambda, LeftPortName, RightPortName>
where
    Lambda: Sized + Eq + Copy + Debug,
    LeftPortName: Eq + Clone,
    RightPortName: Eq,
{
    pub fn new(
        left: Vec<MiddleIndex>,
        right: Vec<MiddleIndex>,
        middle: Vec<Lambda>,
        left_names: Vec<LeftPortName>,
        right_names: Vec<RightPortName>,
    ) -> Self {
        /*
        assumption that left_names and right_names are unique is not checked
        LeftPortName and RightPortName don't have to implement std::hash::Hash here
        so can't enforce with is_unique
        */
        assert!(
            left_names.len() == left.len(),
            "There must be names for everything in the domain and no others"
        );
        assert!(
            right_names.len() == right.len(),
            "There must be names for everything in the codomain and no others"
        );
        Self {
            cospan: Cospan::new(left, right, middle),
            left_names,
            right_names,
        }
    }

    pub fn empty() -> Self {
        Self::new(vec![], vec![], vec![], vec![], vec![])
    }

    pub fn left_names(&self) -> &Vec<LeftPortName> {
        &self.left_names
    }

    pub fn right_names(&self) -> &Vec<RightPortName> {
        &self.right_names
    }

    pub fn identity<T, F>(types: &[Lambda], prenames: &[T], prename_to_name: F) -> Self
    where
        F: Fn(T) -> (LeftPortName, RightPortName),
        T: Copy,
    {
        assert_eq!(types.len(), prenames.len());
        let (left_names, right_names) = prenames.iter().map(|x| prename_to_name(*x)).unzip();
        /*
        assumption that left_names and right_names are unique is not checked
        */

        Self {
            cospan: Cospan::identity(&types.to_vec()),
            left_names,
            right_names,
        }
    }

    #[allow(dead_code)]
    pub fn from_permutation_extra_data<T, F>(
        p: Permutation,
        types: &[Lambda],
        types_as_on_domain: bool,
        prenames: &[T],
        prename_to_name: F,
    ) -> Self
    where
        T: Copy,
        F: Fn(T) -> (LeftPortName, RightPortName),
    {
        /*
        the cospan from a permutation
        the labels are given in types and they are in the same order as either the domain/codomain
            as specified by types_as_on_domain flag
            so if types_as_on_domain is true then the domain side has the labels in the given order
            and the codomain has the labels in the order induced by following the permutation
            vice versa with false
        the prenames and a prename_to_name function is used to produce all the names
            the order is similarly done as the labels using the types_as_on_domain flag
        */
        assert_eq!(types.len(), prenames.len());
        let cospan = Cospan::from_permutation(p.clone(), types, types_as_on_domain);
        let (left_names, right_names) = if types_as_on_domain {
            (
                prenames.iter().map(|pre| prename_to_name(*pre).0).collect(),
                p.inv()
                    .permute(prenames)
                    .iter()
                    .map(|pre| prename_to_name(*pre).1)
                    .collect(),
            )
        } else {
            (
                p.permute(prenames)
                    .iter()
                    .map(|pre| prename_to_name(*pre).0)
                    .collect(),
                prenames.iter().map(|pre| prename_to_name(*pre).1).collect(),
            )
        };
        /*
        assumption that left_names and right_names are unique is not checked
        */

        Self {
            cospan,
            left_names,
            right_names,
        }
    }

    pub fn add_boundary_node_known_target(
        &mut self,
        new_arrow: MiddleIndex,
        new_name: Either<LeftPortName, RightPortName>,
    ) -> Either<LeftIndex, RightIndex> {
        /*
        add a new boundary node that maps to the specified middle index of new_arrow
        name it according to new_name
        which side depends on whether new_name is Left/Right
        */
        self.add_boundary_node(Left(new_arrow), new_name)
    }

    pub fn add_boundary_node_unknown_target(
        &mut self,
        new_arrow: Lambda,
        new_name: Either<LeftPortName, RightPortName>,
    ) -> Either<LeftIndex, RightIndex> {
        /*
        add a new boundary node that maps to a new middle node of specified label new_arrow
        name it according to new_name
        which side depends on whether new_name is Left/Right
        */
        self.add_boundary_node(Right(new_arrow), new_name)
    }

    pub fn add_boundary_node(
        &mut self,
        new_arrow: MiddleIndexOrLambda<Lambda>,
        new_name: Either<LeftPortName, RightPortName>,
    ) -> Either<LeftIndex, RightIndex> {
        /*
        add a new boundary node that maps to a new or existing middle node specified by new_arrow
        name it according to new_name
        which side depends on whether new_name is Left/Right
        panic if new_name would create a repeat
        */
        self.cospan.add_boundary_node(match new_name {
            Left(new_name_real) => {
                assert!(!self.left_names.contains(&new_name_real));
                self.left_names.push(new_name_real);
                Left(new_arrow)
            }
            Right(new_name_real) => {
                assert!(!self.right_names.contains(&new_name_real));
                self.right_names.push(new_name_real);
                Right(new_arrow)
            }
        })
    }

    pub fn delete_boundary_node(&mut self, which_node: Either<LeftIndex, RightIndex>) {
        /*
        deletes a node from one side
        the order is shuffled in this process so also keep the names
        in sync with this change
        CAUTION : relies on knowing that cospan uses swap_remove when deleting a node
            the implementation of delete_boundary_node on Cospan<Lambda>
        */
        match which_node {
            Left(z) => {
                self.left_names.swap_remove(z);
            }
            Right(z) => {
                self.right_names.swap_remove(z);
            }
        }
        self.cospan.delete_boundary_node(which_node);
    }

    #[allow(dead_code)]
    pub fn map_to_same(
        &mut self,
        node_1_name: Either<LeftPortName, RightPortName>,
        node_2_name: Either<LeftPortName, RightPortName>,
    ) -> bool {
        /*
        first find node_1 and node_2 by their names
        if nodes with those names do not exist, then false
        query if the middle nodes that node_1 and node_2 connect to are the same
        */
        let node_1_loc = self.find_node_by_name(node_1_name);
        let node_2_loc = self.find_node_by_name(node_2_name);
        if let Some((node_1_loc_real, node_2_loc_real)) = node_1_loc.zip(node_2_loc) {
            self.cospan.map_to_same(node_1_loc_real, node_2_loc_real)
        } else {
            false
        }
    }

    pub fn connect_pair(
        &mut self,
        node_1_name: Either<LeftPortName, RightPortName>,
        node_2_name: Either<LeftPortName, RightPortName>,
    ) {
        /*
        first find node_1 and node_2 by their names
        if nodes with those names do not exist, then make no change
        collapse the middle nodes that node_1 and node_2 connect to (A and B)
        into a single middle node with the same label as the shared label
        of A and B
        if A and B do not have the same label, give a warning and make no change
        */
        let node_1_loc = self.find_node_by_name(node_1_name);
        let node_2_loc = self.find_node_by_name(node_2_name);
        if let Some((node_1_loc_real, node_2_loc_real)) = node_1_loc.zip(node_2_loc) {
            self.cospan.connect_pair(node_1_loc_real, node_2_loc_real);
        }
    }

    fn find_node_by_name(
        &self,
        desired_name: Either<LeftPortName, RightPortName>,
    ) -> Option<Either<LeftIndex, RightIndex>> {
        /*
        given a name of a node on the domain/codomain give the index in appears in the
        left_names/right_names (those are supposed to have no duplicates
            so each left/right name uniquely specifies a node on the appropriate side,
            there can be repeated names on opposite sides because they will be wrapped in different Left/Right)
        */
        match desired_name {
            Left(desired_name_left) => {
                let index_in_left: Option<LeftIndex> =
                    self.left_names.iter().position(|r| *r == desired_name_left);
                index_in_left.map(Left)
            }
            Right(desired_name_right) => {
                let index_in_right: Option<RightIndex> = self
                    .right_names
                    .iter()
                    .position(|r| *r == desired_name_right);
                index_in_right.map(Right)
            }
        }
    }

    pub fn find_nodes_by_name_predicate<F, G>(
        &self,
        left_pred: F,
        right_pred: G,
        at_most_one: bool,
    ) -> Vec<Either<LeftIndex, RightIndex>>
    where
        F: Fn(LeftPortName) -> bool,
        G: Fn(RightPortName) -> bool,
        LeftPortName: Copy,
        RightPortName: Copy,
    {
        /*
        given predicates on the left names and right names
        find all the left/right indices of nodes with names
        satisfying their appropriate predicates
        if at_most_one, then shortcircuit this so only give the first one found
            do this when know a priori there should <=1 boundary node in the answer
        */
        if at_most_one {
            let index_in_left: Option<LeftIndex> =
                self.left_names.iter().position(|r| left_pred(*r));
            match index_in_left {
                None => {
                    let index_in_right: Option<RightIndex> =
                        self.right_names.iter().position(|r| right_pred(*r));

                    index_in_right.map(Right).into_iter().collect()
                }
                Some(z) => {
                    vec![Left(z)]
                }
            }
        } else {
            let mut matched_indices: Vec<Either<LeftIndex, RightIndex>> = self
                .left_names
                .iter()
                .enumerate()
                .filter_map(|(index, &r)| {
                    if left_pred(r) {
                        Some(Left(index))
                    } else {
                        None
                    }
                })
                .collect();
            let right_indices = self
                .right_names
                .iter()
                .enumerate()
                .filter_map(|(index, &r)| if right_pred(r) { Some(index) } else { None });
            matched_indices.extend(right_indices.map(Right));
            matched_indices
        }
    }

    pub fn delete_boundary_node_by_name(
        &mut self,
        which_node: Either<LeftPortName, RightPortName>,
    ) {
        /*
        find a node by it's name
        if it is not found, there is nothing to delet so give a warning and no change made
        if it is found, delete that node (see delete_boundary_node and the CAUTION therein)
        */
        let which_node_idx = match which_node {
            Left(z) => {
                let index = self.left_names.iter().position(|r| *r == z);
                let Some(idx_left) = index else {
                    warn!("Node to be deleted does not exist. No change made.");
                    return;
                };
                Left(idx_left)
            }
            Right(z) => {
                let index = self.right_names.iter().position(|r| *r == z);
                let Some(idx_right) = index else {
                    warn!("Node to be deleted does not exist. No change made.");
                    return;
                };
                Right(idx_right)
            }
        };
        self.delete_boundary_node(which_node_idx);
    }

    pub fn change_boundary_node_names<FL, FR>(&mut self, f: Either<FL, FR>)
    where
        FL: Fn(&mut LeftPortName),
        FR: Fn(&mut RightPortName),
    {
        /*
        change all boundary names on one side according to a function
        */
        match f {
            Left(left_fun) => {
                for cur_left_name in self.left_names.iter_mut() {
                    left_fun(cur_left_name);
                }
            }
            Right(right_fun) => {
                for cur_right_name in self.right_names.iter_mut() {
                    right_fun(cur_right_name);
                }
            }
        }
    }

    pub fn change_boundary_node_name(
        &mut self,
        name_pair: Either<(LeftPortName, LeftPortName), (RightPortName, RightPortName)>,
    ) {
        /*
        change a name of a boundary node
        if name_pair is Left(old_name,new_name), then look for old_name and if it exists then
        replace that node's name with the new_name
        gives warning and makes no change when there is no node with the desired name
        panic when this would create two nodes on the same side with the same name
        */
        match name_pair {
            Left((z1, z2)) => {
                let Some(idx_left) = self.left_names.iter().position(|r| *r == z1) else {
                    warn!("Node to be changed does not exist. No change made.");
                    return;
                };
                assert!(
                    !self.left_names.iter().any(|r| *r == z2),
                    "There was already a node on the left with the specified new name"
                );
                self.left_names[idx_left] = z2;
            }
            Right((z1, z2)) => {
                let Some(idx_right) = self.right_names.iter().position(|r| *r == z1) else {
                    warn!("Node to be changed does not exist. No change made.");
                    return;
                };
                assert!(
                    !self.right_names.iter().any(|r| *r == z2),
                    "There was already a node on the right with the specified new name"
                );
                self.right_names[idx_right] = z2;
            }
        }
    }

    #[allow(dead_code)]
    pub fn add_middle(&mut self, new_middle: Lambda) {
        /*
        add a new node to the sink with specified label
        */
        self.cospan.add_middle(new_middle);
    }

    pub fn map<F, Mu>(&self, f: F) -> NamedCospan<Mu, LeftPortName, RightPortName>
    where
        F: Fn(Lambda) -> Mu,
        Mu: Sized + Eq + Copy + Debug,
        RightPortName: Clone,
    {
        /*
        change the labels with the function f
        */
        NamedCospan {
            cospan: self.cospan.map(f),
            left_names: self.left_names.clone(),
            right_names: self.right_names.clone(),
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn to_graph<T, U, F, G>(
        &self,
        lambda_decorator: F,
        port_decorator: G,
    ) -> (
        Vec<NodeIndex<DefaultIx>>,
        Vec<NodeIndex<DefaultIx>>,
        Vec<NodeIndex<DefaultIx>>,
        Graph<T, U>,
    )
    where
        F: Fn(Lambda) -> (T, U),
        G: Fn(&mut T, Either<LeftPortName, RightPortName>),
        RightPortName: Clone,
    {
        /*
        make this into a graph
        vertices for every node in left,right and middle
        the vertices are colored by the combined result
            of the first output of lambda_decorator based on their label
            and if they are a port then the port decorator can change this decoration based on that color and their name
        the edges are colored by the second output of lambda_decorator
            based on the (shared) label of their endpoints
        */
        let (left_nodes, middle_nodes, right_nodes, mut graph) =
            self.cospan.to_graph(lambda_decorator);
        for (left_idx, left_node) in left_nodes.iter().enumerate() {
            let cur_left_weight = graph.node_weight_mut(*left_node).unwrap();
            let cur_left_name = Left(self.left_names[left_idx].clone());
            port_decorator(cur_left_weight, cur_left_name);
        }
        for (right_idx, right_node) in right_nodes.iter().enumerate() {
            let cur_right_weight = graph.node_weight_mut(*right_node).unwrap();
            let cur_right_name = Right(self.right_names[right_idx].clone());
            port_decorator(cur_right_weight, cur_right_name);
        }
        (left_nodes, middle_nodes, right_nodes, graph)
    }
}

impl<Lambda, LeftPortName, RightPortName> NamedCospan<Lambda, LeftPortName, RightPortName>
where
    Lambda: Sized + Eq + Copy + Debug,
    LeftPortName: Eq + std::hash::Hash,
    RightPortName: Eq + std::hash::Hash,
{
    #[allow(dead_code)]
    pub fn assert_valid(&self, check_id: bool) {
        self.assert_valid_nohash(check_id);
        assert!(
            crate::utils::is_unique(&self.left_names),
            "There was a duplicate name on the domain"
        );
        assert!(
            crate::utils::is_unique(&self.right_names),
            "There was a duplicate name on the codomain"
        );
    }
}

impl<Lambda, LeftPortName, RightPortName> Monoidal
    for NamedCospan<Lambda, LeftPortName, RightPortName>
where
    Lambda: Sized + Eq + Copy + Debug,
    LeftPortName: Eq + Clone,
    RightPortName: Eq,
{
    fn monoidal(&mut self, other: Self) {
        self.cospan.monoidal(other.cospan);
        /*
        assumption that left_names and right_names are unique is not checked
        there could be something in both self.left_names and other.left_names
        causing a repeat in the new self.left_names
        */
        self.left_names.extend(other.left_names);
        self.right_names.extend(other.right_names);
    }
}

impl<Lambda, LeftPortName, RightPortName> Composable<Vec<Lambda>>
    for NamedCospan<Lambda, LeftPortName, RightPortName>
where
    Lambda: Sized + Eq + Copy + Debug,
    LeftPortName: Eq + Clone,
    RightPortName: Eq + Clone,
{
    fn composable(&self, other: &Self) -> Result<(), CompositionError> {
        self.cospan.composable(&other.cospan)
    }

    fn compose(&self, other: &Self) -> Result<Self, CompositionError> {
        Ok(Self {
            cospan: self.cospan.compose(&other.cospan)?,
            left_names: self.left_names.clone(),
            right_names: other.right_names.clone(),
        })
    }

    fn domain(&self) -> Vec<Lambda> {
        self.cospan.domain()
    }

    fn codomain(&self) -> Vec<Lambda> {
        self.cospan.codomain()
    }
}

impl<Lambda, LeftPortName, RightPortName> MonoidalMorphism<Vec<Lambda>>
    for NamedCospan<Lambda, LeftPortName, RightPortName>
where
    Lambda: Sized + Eq + Copy + Debug,
    LeftPortName: Eq + Clone,
    RightPortName: Eq + Clone,
{
}

impl<Lambda, LeftPortName, RightPortName> SymmetricMonoidalMorphism<Lambda>
    for NamedCospan<Lambda, LeftPortName, RightPortName>
where
    Lambda: Sized + Eq + Copy + Debug,
    LeftPortName: Eq + Clone,
    RightPortName: Eq + Clone,
{
    fn permute_side(&mut self, p: &Permutation, of_right_leg: bool) {
        if of_right_leg {
            in_place_permute(&mut self.right_names, p);
        } else {
            in_place_permute(&mut self.left_names, p);
        }
        self.cospan.permute_side(p, of_right_leg);
    }

    fn from_permutation(_p: Permutation, _types: &[Lambda], _types_as_on_domain: bool) -> Self {
        panic!("Not enough data. Use from_permutation_extra_data instead");
    }
}

mod test {
    #[allow(unused_imports)]
    use crate::{
        category::Composable,
        monoidal::{Monoidal, MonoidalMorphism},
        symmetric_monoidal::SymmetricMonoidalMorphism,
    };

    #[test]
    fn permutatation_manual() {
        use super::NamedCospan;
        use permutations::Permutation;
        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        enum Color {
            Red,
            Green,
            Blue,
        }
        let full_types: Vec<Color> = vec![Color::Red, Color::Green, Color::Blue];
        let type_names_on_source = true;
        let cospan = NamedCospan::<Color, Color, Color>::from_permutation_extra_data(
            Permutation::rotation_left(3, 1),
            &full_types,
            type_names_on_source,
            &full_types,
            |z| (z, z),
        );
        let cospan_2 = NamedCospan::<Color, Color, Color>::from_permutation_extra_data(
            Permutation::rotation_left(3, 2),
            &vec![Color::Blue, Color::Red, Color::Green],
            type_names_on_source,
            &vec![Color::Green, Color::Blue, Color::Red],
            |z| (z, z),
        );
        let mid_interface_1 = cospan.codomain();
        let mid_interface_2 = cospan_2.domain();
        let comp = cospan.compose(&cospan_2);
        match comp {
            Ok(real_res) => {
                let expected_res = NamedCospan::identity(&full_types, &full_types, |z| (z, z));
                assert_eq!(expected_res.domain(), real_res.domain());
                assert_eq!(expected_res.codomain(), real_res.codomain());
            }
            Err(_e) => {
                panic!(
                    "Could not compose simple example because {:?} did not match {:?}",
                    mid_interface_1, mid_interface_2
                );
            }
        }

        let type_names_on_source = false;
        let cospan = NamedCospan::<Color, Color, Color>::from_permutation_extra_data(
            Permutation::rotation_left(3, 1),
            &full_types,
            type_names_on_source,
            &full_types,
            |z| (z, z),
        );
        let cospan_2 = NamedCospan::<Color, Color, Color>::from_permutation_extra_data(
            Permutation::rotation_left(3, 2),
            &vec![Color::Green, Color::Blue, Color::Red],
            type_names_on_source,
            &vec![Color::Green, Color::Blue, Color::Red],
            |z| (z, z),
        );
        let mid_interface_1 = cospan.codomain();
        let mid_interface_2 = cospan_2.domain();
        let comp = cospan.compose(&cospan_2);
        match comp {
            Ok(real_res) => {
                let expected_res = NamedCospan::identity(
                    &vec![Color::Green, Color::Blue, Color::Red],
                    &vec![Color::Green, Color::Blue, Color::Red],
                    |z| (z, z),
                );
                assert_eq!(expected_res.domain(), real_res.domain());
                assert_eq!(expected_res.codomain(), real_res.codomain());
            }
            Err(_e) => {
                panic!(
                    "Could not compose simple example because {:?} did not match {:?}",
                    mid_interface_1, mid_interface_2
                );
            }
        }
    }

    #[test]
    fn permutatation_automatic() {
        use super::NamedCospan;
        use crate::utils::rand_perm;
        use rand::distributions::Uniform;
        use rand::prelude::Distribution;
        let n_max = 10;
        let between = Uniform::<usize>::from(2..n_max);
        let mut rng = rand::thread_rng();
        let n = between.sample(&mut rng);

        for trial_num in 0..20 {
            let types_as_on_source = trial_num % 2 == 0;
            let p1 = rand_perm(n, n * 2);
            let p2 = rand_perm(n, n * 2);
            let prod = p1.clone() * p2.clone();
            let cospan_p1 = NamedCospan::from_permutation_extra_data(
                p1,
                &(0..n).map(|_| ()).collect::<Vec<_>>(),
                types_as_on_source,
                &(0..n).map(|z| z).collect::<Vec<usize>>(),
                |_| ((), ()),
            );
            let cospan_p2 = NamedCospan::from_permutation_extra_data(
                p2,
                &(0..n).map(|_| ()).collect::<Vec<_>>(),
                types_as_on_source,
                &(0..n).map(|z| z).collect::<Vec<_>>(),
                |_| ((), ()),
            );
            let cospan_prod = cospan_p1.compose(&cospan_p2);
            match cospan_prod {
                Ok(real_res) => {
                    let expected_res = NamedCospan::from_permutation_extra_data(
                        prod,
                        &(0..n).map(|_| ()).collect::<Vec<_>>(),
                        types_as_on_source,
                        &(0..n).map(|z| z).collect::<Vec<usize>>(),
                        |_| ((), ()),
                    );
                    assert_eq!(real_res.domain(), expected_res.domain());
                    assert_eq!(real_res.codomain(), expected_res.codomain());
                    assert_eq!(real_res.left_names, expected_res.left_names);
                    assert_eq!(real_res.right_names, expected_res.right_names);
                    assert_eq!(
                        real_res.cospan.left_to_middle(),
                        expected_res.cospan.left_to_middle()
                    );
                    assert_eq!(
                        real_res.cospan.right_to_middle(),
                        expected_res.cospan.right_to_middle()
                    );
                }
                Err(e) => {
                    panic!("Could not compose simple example {:?}", e)
                }
            }
        }
    }
}
