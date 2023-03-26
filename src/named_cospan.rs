use either::Either::{self, Left, Right};
use log::warn;
use permutations::Permutation;
use petgraph::{matrix_graph::NodeIndex, prelude::Graph, stable_graph::DefaultIx};

use crate::{cospan::Cospan, utils::to_vec_01};

type LeftIndex = usize;
type RightIndex = usize;
type MiddleIndex = usize;
type MiddleIndexOrLambda<Lambda> = Either<MiddleIndex, Lambda>;

pub struct NamedCospan<Lambda: Sized + Eq + Copy, LeftPortName, RightPortName> {
    underlying_cospan: Cospan<Lambda>,
    left_names: Vec<LeftPortName>,
    right_names: Vec<RightPortName>,
}

impl<'a, Lambda, LeftPortName, RightPortName> NamedCospan<Lambda, LeftPortName, RightPortName>
where
    Lambda: Sized + Eq + Copy,
    LeftPortName: Eq,
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

    #[allow(dead_code)]
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
        prenames: &[T],
        prename_to_name: F,
    ) -> Self
    where
        F: Fn(T) -> (LeftPortName, RightPortName),
        T: Copy,
    {
        assert_eq!(types.len(), prenames.len());
        let underlying_cospan = Cospan::<Lambda>::from_permutation(p.clone(), types);
        let left_names = prenames.iter().map(|pre| prename_to_name(*pre).0).collect();
        let right_names = p
            .permute(prenames)
            .iter()
            .map(|pre| prename_to_name(*pre).1)
            .collect();
        //todo!("Might have mixed up p and p inverse");
        Self {
            underlying_cospan,
            left_names,
            right_names,
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

    #[allow(dead_code)]
    pub fn add_middle(&mut self, new_middle: Lambda) {
        self.underlying_cospan.add_middle(new_middle);
    }

    #[allow(dead_code)]
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

    #[allow(dead_code)]
    pub fn compose(self, other: Self) -> Result<Self, &'static str> {
        let new_underlying = self.underlying_cospan.compose(other.underlying_cospan)?;
        Ok(Self {
            underlying_cospan: new_underlying,
            left_names: self.left_names,
            right_names: other.right_names,
        })
    }
}
