use either::Either::{self, Left, Right};
use log::warn;
use permutations::Permutation;
use petgraph::{matrix_graph::NodeIndex, prelude::Graph, stable_graph::DefaultIx};
use std::fmt::Debug;

use crate::category::{Composable, HasIdentity};
use crate::cospan::Cospan;
use crate::monoidal::{Monoidal, MonoidalMorphism};
use crate::symmetric_monoidal::SymmetricMonoidalMorphism;
use crate::utils::{in_place_permute, to_vec_01};

type LeftIndex = usize;
type RightIndex = usize;
type MiddleIndex = usize;
type MiddleIndexOrLambda<Lambda> = Either<MiddleIndex, Lambda>;

pub struct NamedCospan<Lambda: Sized + Eq + Copy + Debug, LeftPortName, RightPortName> {
    underlying_cospan: Cospan<Lambda>,
    left_names: Vec<LeftPortName>,
    right_names: Vec<RightPortName>,
}

impl<'a, Lambda, LeftPortName, RightPortName> NamedCospan<Lambda, LeftPortName, RightPortName>
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
        let underlying_cospan = Cospan::<Lambda>::new(left, right, middle);
        Self {
            underlying_cospan,
            left_names,
            right_names,
        }
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
        let underlying_cospan = Cospan::<Lambda>::identity(&types.to_vec());
        let left_names = prenames.iter().map(|pre| prename_to_name(*pre).0).collect();
        let right_names = prenames.iter().map(|pre| prename_to_name(*pre).1).collect();
        Self {
            underlying_cospan,
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
        assert_eq!(types.len(), prenames.len());
        let underlying_cospan =
            Cospan::<Lambda>::from_permutation(p.clone(), &types.to_vec(), types_as_on_domain);
        if types_as_on_domain {
            let left_names = prenames.iter().map(|pre| prename_to_name(*pre).0).collect();
            let right_names = p
                .inv()
                .permute(prenames)
                .iter()
                .map(|pre| prename_to_name(*pre).1)
                .collect();
            Self {
                underlying_cospan,
                left_names,
                right_names,
            }
        } else {
            let left_names = p
                .permute(prenames)
                .iter()
                .map(|pre| prename_to_name(*pre).0)
                .collect();
            let right_names = prenames.iter().map(|pre| prename_to_name(*pre).1).collect();
            Self {
                underlying_cospan,
                left_names,
                right_names,
            }
        }
    }

    pub fn add_boundary_node_known_target(
        &mut self,
        new_arrow: MiddleIndex,
        new_name: Either<LeftPortName, RightPortName>,
    ) -> Either<LeftIndex, RightIndex> {
        self.add_boundary_node(Left(new_arrow), new_name)
    }

    pub fn add_boundary_node_unknown_target(
        &mut self,
        new_arrow: Lambda,
        new_name: Either<LeftPortName, RightPortName>,
    ) -> Either<LeftIndex, RightIndex> {
        self.add_boundary_node(Right(new_arrow), new_name)
    }

    pub fn add_boundary_node(
        &mut self,
        new_arrow: MiddleIndexOrLambda<Lambda>,
        new_name: Either<LeftPortName, RightPortName>,
    ) -> Either<LeftIndex, RightIndex> {
        match new_name {
            Left(new_name_real) => {
                self.left_names.push(new_name_real);
                self.underlying_cospan.add_boundary_node(Left(new_arrow))
            }
            Right(new_name_real) => {
                self.right_names.push(new_name_real);
                self.underlying_cospan.add_boundary_node(Right(new_arrow))
            }
        }
    }

    pub fn delete_boundary_node(&mut self, which_node: Either<LeftIndex, RightIndex>) {
        match which_node {
            Left(z) => {
                self.left_names.swap_remove(z);
            }
            Right(z) => {
                self.right_names.swap_remove(z);
            }
        }
        self.underlying_cospan.delete_boundary_node(which_node);
    }

    pub fn connect_pair(
        &mut self,
        node_1: Either<LeftPortName, RightPortName>,
        node_2: Either<LeftPortName, RightPortName>,
    ) {
        let node_1_loc = self.find_node_by_name(node_1);
        let node_2_loc = self.find_node_by_name(node_2);
        if let (Some(node_1_loc_real), Some(node_2_loc_real)) = (node_1_loc, node_2_loc) {
            self.underlying_cospan
                .connect_pair(node_1_loc_real, node_2_loc_real);
        }
    }

    fn find_node_by_name(
        &self,
        desired_name: Either<LeftPortName, RightPortName>,
    ) -> Option<Either<LeftIndex, RightIndex>> {
        match desired_name {
            Left(desired_name_left) => {
                let index_in_left: Option<LeftIndex> =
                    self.left_names.iter().position(|r| *r == desired_name_left);
                index_in_left.map(Left)
            }
            Right(desired_name_right) => {
                let index_in_right: Option<LeftIndex> = self
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
        if at_most_one {
            let index_in_left: Option<LeftIndex> =
                self.left_names.iter().position(|r| left_pred(*r));
            match index_in_left {
                None => {
                    let index_in_right: Option<RightIndex> =
                        self.right_names.iter().position(|r| right_pred(*r));
                    to_vec_01(index_in_right.map(Right))
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
        let which_node_idx = match which_node {
            Left(z) => {
                let index = self.left_names.iter().position(|r| *r == z);
                match index {
                    None => {
                        warn!("Node to be deleted does not exist. No change made.");
                        return;
                    }
                    Some(idx_left) => Left(idx_left),
                }
            }
            Right(z) => {
                let index = self.right_names.iter().position(|r| *r == z);
                match index {
                    None => {
                        warn!("Node to be deleted does not exist. No change made.");
                        return;
                    }
                    Some(idx_right) => Right(idx_right),
                }
            }
        };
        self.delete_boundary_node(which_node_idx);
    }

    pub fn change_boundary_node_name(
        &mut self,
        name_pair: Either<(LeftPortName, LeftPortName), (RightPortName, RightPortName)>,
    ) {
        match name_pair {
            Left((z1, z2)) => {
                let index = self.left_names.iter().position(|r| *r == z1);
                match index {
                    None => {
                        warn!("Node to be changed does not exist. No change made.");
                    }
                    Some(idx_left) => {
                        self.left_names[idx_left] = z2;
                    }
                }
            }
            Right((z1, z2)) => {
                let index = self.right_names.iter().position(|r| *r == z1);
                match index {
                    None => {
                        warn!("Node to be changed does not exist. No change made.");
                    }
                    Some(idx_right) => {
                        self.right_names[idx_right] = z2;
                    }
                }
            }
        }
    }

    #[allow(dead_code)]
    pub fn add_middle(&mut self, new_middle: Lambda) {
        self.underlying_cospan.add_middle(new_middle);
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
        let (left_nodes, middle_nodes, right_nodes, mut graph) =
            self.underlying_cospan.to_graph(lambda_decorator);
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

impl<Lambda, LeftPortName, RightPortName> Monoidal
    for NamedCospan<Lambda, LeftPortName, RightPortName>
where
    Lambda: Sized + Eq + Copy + Debug,
    LeftPortName: Eq + Clone,
    RightPortName: Eq,
{
    fn monoidal(&mut self, other: Self) {
        self.underlying_cospan.monoidal(other.underlying_cospan);
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
    fn composable(&self, other: &Self) -> Result<(), String> {
        self.underlying_cospan.composable(&other.underlying_cospan)
    }

    fn compose(&self, other: &Self) -> Result<Self, String> {
        let new_underlying = self.underlying_cospan.compose(&other.underlying_cospan)?;
        Ok(Self {
            underlying_cospan: new_underlying,
            left_names: self.left_names.clone(),
            right_names: other.right_names.clone(),
        })
    }

    fn domain(&self) -> Vec<Lambda> {
        self.underlying_cospan.domain()
    }

    fn codomain(&self) -> Vec<Lambda> {
        self.underlying_cospan.codomain()
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
        self.underlying_cospan.permute_side(p, of_right_leg);
    }

    fn from_permutation(_p: Permutation, _types: &[Lambda], _types_as_on_domain: bool) -> Self {
        panic!("Not enough data. Use from_permutation_extra_data instead");
    }
}

mod test {
    #[allow(unused_imports)]
    use crate::category::Composable;
    #[allow(unused_imports)]
    use crate::monoidal::{Monoidal, MonoidalMorphism};
    #[allow(unused_imports)]
    use crate::symmetric_monoidal::SymmetricMonoidalMorphism;

    #[test]
    fn permutatation_manual() {
        use super::NamedCospan;
        use permutations::Permutation;
        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        enum COLOR {
            RED,
            GREEN,
            BLUE,
        }
        let full_types: Vec<COLOR> = vec![COLOR::RED, COLOR::GREEN, COLOR::BLUE];
        let type_names_on_source = true;
        let my_cospan = NamedCospan::<COLOR, COLOR, COLOR>::from_permutation_extra_data(
            Permutation::rotation_left(3, 1),
            &full_types,
            type_names_on_source,
            &full_types,
            |z| (z, z),
        );
        let my_cospan_2 = NamedCospan::<COLOR, COLOR, COLOR>::from_permutation_extra_data(
            Permutation::rotation_left(3, 2),
            &vec![COLOR::BLUE, COLOR::RED, COLOR::GREEN],
            type_names_on_source,
            &vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED],
            |z| (z, z),
        );
        let my_mid_interface_1 = my_cospan.codomain();
        let my_mid_interface_2 = my_cospan_2.domain();
        let comp = my_cospan.compose(&my_cospan_2);
        match comp {
            Ok(real_res) => {
                let expected_res = NamedCospan::identity(&full_types, &full_types, |z| (z, z));
                assert_eq!(expected_res.domain(), real_res.domain());
                assert_eq!(expected_res.codomain(), real_res.codomain());
            }
            Err(_e) => {
                panic!(
                    "Could not compose simple example because {:?} did not match {:?}",
                    my_mid_interface_1, my_mid_interface_2
                );
            }
        }

        let type_names_on_source = false;
        let my_cospan = NamedCospan::<COLOR, COLOR, COLOR>::from_permutation_extra_data(
            Permutation::rotation_left(3, 1),
            &full_types,
            type_names_on_source,
            &full_types,
            |z| (z, z),
        );
        let my_cospan_2 = NamedCospan::<COLOR, COLOR, COLOR>::from_permutation_extra_data(
            Permutation::rotation_left(3, 2),
            &vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED],
            type_names_on_source,
            &vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED],
            |z| (z, z),
        );
        let my_mid_interface_1 = my_cospan.codomain();
        let my_mid_interface_2 = my_cospan_2.domain();
        let comp = my_cospan.compose(&my_cospan_2);
        match comp {
            Ok(real_res) => {
                let expected_res = NamedCospan::identity(
                    &vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED],
                    &vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED],
                    |z| (z, z),
                );
                assert_eq!(expected_res.domain(), real_res.domain());
                assert_eq!(expected_res.codomain(), real_res.codomain());
            }
            Err(_e) => {
                panic!(
                    "Could not compose simple example because {:?} did not match {:?}",
                    my_mid_interface_1, my_mid_interface_2
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
        let my_n = between.sample(&mut rng);

        for trial_num in 0..20 {
            let types_as_on_source = trial_num % 2 == 0;
            let p1 = rand_perm(my_n, my_n * 2);
            let p2 = rand_perm(my_n, my_n * 2);
            let prod = p1.clone() * p2.clone();
            let cospan_p1 = NamedCospan::from_permutation_extra_data(
                p1,
                &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
                types_as_on_source,
                &(0..my_n).map(|z| z).collect::<Vec<usize>>(),
                |_| ((), ()),
            );
            let cospan_p2 = NamedCospan::from_permutation_extra_data(
                p2,
                &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
                types_as_on_source,
                &(0..my_n).map(|z| z).collect::<Vec<usize>>(),
                |_| ((), ()),
            );
            let cospan_prod = cospan_p1.compose(&cospan_p2);
            match cospan_prod {
                Ok(real_res) => {
                    let expected_res = NamedCospan::from_permutation_extra_data(
                        prod,
                        &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
                        types_as_on_source,
                        &(0..my_n).map(|z| z).collect::<Vec<usize>>(),
                        |_| ((), ()),
                    );
                    assert_eq!(real_res.domain(), expected_res.domain());
                    assert_eq!(real_res.codomain(), expected_res.codomain());
                    assert_eq!(real_res.left_names, expected_res.left_names);
                    assert_eq!(real_res.right_names, expected_res.right_names);
                    assert_eq!(
                        real_res.underlying_cospan.left_to_middle(),
                        expected_res.underlying_cospan.left_to_middle()
                    );
                    assert_eq!(
                        real_res.underlying_cospan.right_to_middle(),
                        expected_res.underlying_cospan.right_to_middle()
                    );
                }
                Err(e) => {
                    panic!("Could not compose simple example {:?}", e)
                }
            }
        }
    }
}
