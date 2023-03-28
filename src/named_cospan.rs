use either::Either::{self, Left, Right};
use log::warn;
use permutations::Permutation;
use petgraph::{matrix_graph::NodeIndex, prelude::Graph, stable_graph::DefaultIx};
use std::fmt::Debug;

use crate::cospan::Cospan;
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

    pub fn left_interface(&self) -> Vec<Lambda> {
        self.underlying_cospan.left_interface()
    }

    #[allow(dead_code)]
    pub fn right_interface(&self) -> Vec<Lambda> {
        self.underlying_cospan.right_interface()
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
        let underlying_cospan = Cospan::<Lambda>::identity(types);
        let left_names = prenames.iter().map(|pre| prename_to_name(*pre).0).collect();
        let right_names = prenames.iter().map(|pre| prename_to_name(*pre).1).collect();
        Self {
            underlying_cospan,
            left_names,
            right_names,
        }
    }

    #[allow(dead_code)]
    pub fn from_permutation<T, F>(
        p: Permutation,
        types: &[Lambda],
        types_names_as_on_source: bool,
        prenames: &[T],
        prename_to_name: F,
    ) -> Self
    where
        F: Fn(T) -> (LeftPortName, RightPortName),
        T: Copy,
    {
        assert_eq!(types.len(), prenames.len());
        let underlying_cospan =
            Cospan::<Lambda>::from_permutation(p.clone(), types, types_names_as_on_source);
        if types_names_as_on_source {
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

    pub fn permute_leg(&mut self, p: &Permutation, of_right_leg: bool) {
        if of_right_leg {
            in_place_permute(&mut self.right_names, p);
        } else {
            in_place_permute(&mut self.left_names, p);
        }
        self.underlying_cospan.permute_leg(p, of_right_leg);
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

    #[allow(dead_code)]
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

    pub fn monoidal(&mut self, other: Self) {
        self.underlying_cospan.monoidal(other.underlying_cospan);
        self.left_names.extend(other.left_names);
        self.right_names.extend(other.right_names);
    }

    #[allow(clippy::type_complexity)]
    pub fn to_graph<T, U, V, F, G>(
        &self,
        lambda_decorator: F,
        _port_decorator: G,
    ) -> (
        Vec<NodeIndex<DefaultIx>>,
        Vec<NodeIndex<DefaultIx>>,
        Vec<NodeIndex<DefaultIx>>,
        Graph<T, U>,
    )
    where
        F: Fn(Lambda) -> (T, U),
        G: Fn(Either<LeftPortName, RightPortName>) -> V,
    {
        let (left_nodes, middle_nodes, right_nodes, graph) =
            self.underlying_cospan.to_graph(lambda_decorator);
        (left_nodes, middle_nodes, right_nodes, graph)
    }

    pub fn compose(&self, other: Self) -> Result<Self, String> {
        let new_underlying = self
            .underlying_cospan
            .clone()
            .compose(other.underlying_cospan)?;
        Ok(Self {
            underlying_cospan: new_underlying,
            left_names: self.left_names.clone(),
            right_names: other.right_names,
        })
    }
}

mod test {

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
        let my_cospan = NamedCospan::<COLOR, COLOR, COLOR>::from_permutation(
            Permutation::rotation_left(3, 1),
            &full_types,
            type_names_on_source,
            &full_types,
            |z| (z, z),
        );
        let my_cospan_2 = NamedCospan::<COLOR, COLOR, COLOR>::from_permutation(
            Permutation::rotation_left(3, 2),
            &vec![COLOR::BLUE, COLOR::RED, COLOR::GREEN],
            type_names_on_source,
            &vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED],
            |z| (z, z),
        );
        let my_mid_interface_1 = my_cospan.right_interface();
        let my_mid_interface_2 = my_cospan_2.left_interface();
        let comp = my_cospan.compose(my_cospan_2);
        match comp {
            Ok(real_res) => {
                let expected_res = NamedCospan::identity(&full_types, &full_types, |z| (z, z));
                assert_eq!(
                    expected_res.underlying_cospan.left_interface(),
                    real_res.underlying_cospan.left_interface()
                );
                assert_eq!(
                    expected_res.underlying_cospan.right_interface(),
                    real_res.underlying_cospan.right_interface()
                );
            }
            Err(_e) => {
                panic!(
                    "Could not compose simple example because {:?} did not match {:?}",
                    my_mid_interface_1, my_mid_interface_2
                );
            }
        }

        let type_names_on_source = false;
        let my_cospan = NamedCospan::<COLOR, COLOR, COLOR>::from_permutation(
            Permutation::rotation_left(3, 1),
            &full_types,
            type_names_on_source,
            &full_types,
            |z| (z, z),
        );
        let my_cospan_2 = NamedCospan::<COLOR, COLOR, COLOR>::from_permutation(
            Permutation::rotation_left(3, 2),
            &vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED],
            type_names_on_source,
            &vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED],
            |z| (z, z),
        );
        let my_mid_interface_1 = my_cospan.right_interface();
        let my_mid_interface_2 = my_cospan_2.left_interface();
        let comp = my_cospan.compose(my_cospan_2);
        match comp {
            Ok(real_res) => {
                let expected_res = NamedCospan::identity(
                    &vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED],
                    &vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED],
                    |z| (z, z),
                );
                assert_eq!(
                    expected_res.underlying_cospan.left_interface(),
                    real_res.underlying_cospan.left_interface()
                );
                assert_eq!(
                    expected_res.underlying_cospan.right_interface(),
                    real_res.underlying_cospan.right_interface()
                );
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
            let cospan_p1 = NamedCospan::from_permutation(
                p1,
                &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
                types_as_on_source,
                &(0..my_n).map(|z| z).collect::<Vec<usize>>(),
                |_| ((), ()),
            );
            let cospan_p2 = NamedCospan::from_permutation(
                p2,
                &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
                types_as_on_source,
                &(0..my_n).map(|z| z).collect::<Vec<usize>>(),
                |_| ((), ()),
            );
            let cospan_prod = cospan_p1.compose(cospan_p2);
            match cospan_prod {
                Ok(real_res) => {
                    let expected_res = NamedCospan::from_permutation(
                        prod,
                        &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
                        types_as_on_source,
                        &(0..my_n).map(|z| z).collect::<Vec<usize>>(),
                        |_| ((), ()),
                    );
                    assert_eq!(real_res.left_interface(), expected_res.left_interface());
                    assert_eq!(real_res.right_interface(), expected_res.right_interface());
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
