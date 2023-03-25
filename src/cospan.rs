use either::Either::{self, Left, Right};
use petgraph::{prelude::Graph, stable_graph::DefaultIx, stable_graph::NodeIndex};
use std::collections::HashMap;
use union_find::{UnionBySize, UnionFind};

use crate::finset::FinSetMap;
use crate::utils::{bimap, represents_id};

type LeftIndex = usize;
type RightIndex = usize;
type MiddleIndex = usize;
type MiddleIndexOrLambda<Lambda> = Either<MiddleIndex, Lambda>;

pub struct Cospan<Lambda: Sized + Eq + Copy> {
    left: Vec<MiddleIndex>,
    right: Vec<MiddleIndex>,
    middle: Vec<Lambda>,
    is_left_id: bool,
    is_right_id: bool,
}

impl<'a, Lambda> Cospan<Lambda>
where
    Lambda: Sized + Eq + Copy,
{
    pub fn assert_valid(&self, check_id: bool) {
        let middle_size = self.middle.len();
        let left_in_bounds = self.left.iter().all(|z| *z < middle_size);
        assert!(
            left_in_bounds,
            "A target for one of the left arrows was out of bounds"
        );
        let right_in_bounds = self.right.iter().all(|z| *z < middle_size);
        assert!(
            right_in_bounds,
            "A target for one of the right arrows was out of bounds"
        );
        if check_id {
            let is_left_really_id = represents_id(&self.left);
            assert_eq!(
                is_left_really_id, self.is_left_id,
                "The identity nature of the left arrow was wrong"
            );
            let is_right_really_id = represents_id(&self.right);
            assert_eq!(
                is_right_really_id, self.is_right_id,
                "The identity nature of the right arrow was wrong"
            );
        }
    }

    pub fn new(left: Vec<MiddleIndex>, right: Vec<MiddleIndex>, middle: Vec<Lambda>) -> Self {
        let is_left_id = represents_id(&left);
        let is_right_id = represents_id(&right);
        let answer = Self {
            left,
            right,
            middle,
            is_left_id,
            is_right_id,
        };
        answer.assert_valid(false);
        answer
    }

    pub fn identity(types: &[Lambda]) -> Self {
        let num_types = types.len();
        Self {
            left: (0..num_types).collect(),
            right: (0..num_types).collect(),
            middle: types.to_vec(),
            is_left_id: true,
            is_right_id: true,
        }
    }

    #[allow(dead_code)]
    pub fn add_boundary_node_known_target(
        &mut self,
        new_arrow: Either<MiddleIndex, MiddleIndex>,
    ) -> Either<LeftIndex, RightIndex> {
        self.add_boundary_node(bimap(new_arrow, |z| Left(z), |z| Left(z)))
    }

    #[allow(dead_code)]
    pub fn add_boundary_node_unknown_target(
        &mut self,
        new_arrow: Either<Lambda, Lambda>,
    ) -> Either<LeftIndex, RightIndex> {
        self.add_boundary_node(bimap(new_arrow, |z| Right(z), |z| Right(z)))
    }

    pub fn add_boundary_node(
        &mut self,
        new_arrow: Either<MiddleIndexOrLambda<Lambda>, MiddleIndexOrLambda<Lambda>>,
    ) -> Either<LeftIndex, RightIndex> {
        if let Left(tgt_info) = new_arrow {
            match tgt_info {
                Left(tgt_idx) => {
                    self.left.push(tgt_idx);
                    self.is_left_id &= self.left.len() - 1 == tgt_idx;
                }
                Right(new_lambda) => {
                    self.left.push(self.middle.len());
                    self.middle.push(new_lambda);
                    self.is_left_id &= self.left.len() == self.middle.len();
                }
            }
            Left(self.left.len() - 1)
        } else if let Right(tgt_info) = new_arrow {
            match tgt_info {
                Left(tgt_idx) => {
                    self.right.push(tgt_idx);
                    self.is_right_id &= self.right.len() - 1 == tgt_idx;
                }
                Right(new_lambda) => {
                    self.right.push(self.middle.len());
                    self.middle.push(new_lambda);
                    self.is_right_id &= self.right.len() == self.middle.len();
                }
            }
            Right(self.right.len() - 1)
        } else {
            panic!("All possibilities destructured. Unreachable");
        }
    }

    pub fn delete_boundary_node(&mut self, which_node: Either<LeftIndex, RightIndex>) {
        match which_node {
            Left(z) => {
                self.is_left_id &= z == self.left.len() - 1;
                self.left.swap_remove(z);
            }
            Right(z) => {
                self.is_right_id &= z == self.right.len() - 1;
                self.right.swap_remove(z);
            }
        }
    }

    pub fn add_middle(&mut self, new_middle: Lambda) -> MiddleIndex {
        self.middle.push(new_middle);
        self.is_left_id = false;
        self.is_right_id = false;
        self.middle.len() - 1
    }

    pub fn monoidal(&mut self, mut other: Self) {
        let middle_shift = self.middle.len();
        other.left.iter_mut().for_each(|v| *v += middle_shift);
        other.right.iter_mut().for_each(|v| *v += middle_shift);
        self.left.extend(other.left);
        self.right.extend(other.right);
        self.middle.extend(other.middle);
        self.is_left_id &= other.is_left_id;
        self.is_right_id &= other.is_right_id;
    }

    #[allow(clippy::type_complexity)]
    pub fn to_graph<T, U, F>(
        &self,
        lambda_decorator: F,
    ) -> (
        Vec<NodeIndex<DefaultIx>>,
        Vec<NodeIndex<DefaultIx>>,
        Vec<NodeIndex<DefaultIx>>,
        Graph<T, U>,
    )
    where
        F: Fn(Lambda) -> (T, U),
    {
        let mut graph = Graph::<T, U>::new();
        let mut all_middle_nodes: Vec<NodeIndex<DefaultIx>> = Vec::with_capacity(self.middle.len());
        for cur_mid in &self.middle {
            let (node_dec, _) = lambda_decorator(*cur_mid);
            let cur_mid_node: NodeIndex<DefaultIx> = graph.add_node(node_dec);
            all_middle_nodes.push(cur_mid_node);
        }
        let mut all_left_nodes: Vec<NodeIndex<DefaultIx>> = Vec::with_capacity(self.left.len());
        for cur_left_target in &self.left {
            let (node_dec, edge_dec) = lambda_decorator(self.middle[*cur_left_target]);
            let cur_left_node: NodeIndex<DefaultIx> = graph.add_node(node_dec);
            all_left_nodes.push(cur_left_node);
            graph.add_edge(cur_left_node, all_middle_nodes[*cur_left_target], edge_dec);
        }
        let mut all_right_nodes: Vec<NodeIndex<DefaultIx>> = Vec::with_capacity(self.left.len());
        for cur_right_target in &self.right {
            let (node_dec, edge_dec) = lambda_decorator(self.middle[*cur_right_target]);
            let cur_right_node: NodeIndex<DefaultIx> = graph.add_node(node_dec);
            all_right_nodes.push(cur_right_node);
            graph.add_edge(
                cur_right_node,
                all_middle_nodes[*cur_right_target],
                edge_dec,
            );
        }
        (all_left_nodes, all_middle_nodes, all_right_nodes, graph)
    }

    pub fn compose(self, other: Self) -> Result<Self, &'static str> {
        let mut self_interface = self.right.iter().map(|mid| self.middle[*mid]);
        let mut other_interface = other.left.iter().map(|mid| other.middle[*mid]);
        let mut to_continue = true;
        while to_continue {
            let current_self = self_interface.next();
            let current_other = other_interface.next();
            match (current_self, current_other) {
                (None, None) => {
                    to_continue = false;
                }
                (Some(_), None) => {
                    return Err("Mismatch in cardinalities of common interface");
                }
                (None, Some(_)) => {
                    return Err("Mismatch in cardinalities of common interface");
                }
                (Some(w1), Some(w2)) => {
                    if w1 != w2 {
                        return Err("Mismatch in labels of common interface");
                    }
                }
            }
        }

        let (pushout_target, left_to_pushout, right_to_pushout, representative) =
            perform_pushout::<crate::QuickUnionUf<crate::UnionBySize>, Lambda>(
                &self.right,
                self.middle.len(),
                self.is_right_id,
                &other.left,
                other.middle.len(),
                other.is_left_id,
            )?;
        let mut composition = Cospan::<Lambda>::new(
            Vec::with_capacity(self.left.len()),
            Vec::with_capacity(other.right.len()),
            Vec::with_capacity(pushout_target),
        );
        for repr in representative {
            let lambda_assign = match repr {
                Left(z) => self.middle[z],
                Right(z) => other.middle[z],
            };
            composition.add_middle(lambda_assign);
        }
        for target_in_self_middle in self.left {
            let target_in_pushout = left_to_pushout[target_in_self_middle];
            composition.add_boundary_node(Left(Left(target_in_pushout)));
        }
        for target_in_other_middle in other.right {
            let target_in_pushout = right_to_pushout[target_in_other_middle];
            composition.add_boundary_node(Right(Left(target_in_pushout)));
        }
        Ok(composition)
    }
}

type PushoutResult = (
    MiddleIndex,
    Vec<MiddleIndex>,
    Vec<MiddleIndex>,
    Vec<Either<LeftIndex, RightIndex>>,
);
fn perform_pushout<T, Lambda: Eq>(
    left_leg: &[LeftIndex],
    left_leg_max_target: LeftIndex,
    left_leg_id: bool,
    right_leg: &[RightIndex],
    right_leg_max_target: RightIndex,
    right_leg_id: bool,
) -> Result<PushoutResult, &'static str>
where
    T: UnionFind<UnionBySize>,
{
    if left_leg.len() != right_leg.len() {
        return Err("Mismatch in cardinalities of common interface");
    }
    if left_leg_id {
        let pushout_target = right_leg_max_target;
        let left_to_pushout = right_leg.to_vec();
        let right_to_pushout = (0..right_leg_max_target).collect::<FinSetMap>();
        let representative = (0..right_leg_max_target).map(Right);
        return Ok((
            pushout_target,
            left_to_pushout,
            right_to_pushout,
            representative.collect(),
        ));
    }
    if right_leg_id {
        let pushout_target = left_leg_max_target;
        let right_to_pushout = left_leg.to_vec();
        let left_to_pushout = (0..left_leg_max_target).collect::<FinSetMap>();
        let representative = (0..left_leg_max_target).map(Left);
        return Ok((
            pushout_target,
            left_to_pushout,
            right_to_pushout,
            representative.collect(),
        ));
    }

    let mut uf = T::new(left_leg_max_target + right_leg_max_target);
    for idx in 0..left_leg.len() {
        let left_z = left_leg[idx];
        let right_z = right_leg[idx] + left_leg_max_target;
        uf.union(left_z, right_z);
    }
    let mut set_to_part_num = HashMap::new();
    let mut current_set_number = 0;
    let mut left_to_pushout: Vec<MiddleIndex> = Vec::with_capacity(left_leg_max_target);
    let expected_num_sets = uf.size();
    let mut representative = Vec::with_capacity(expected_num_sets);
    for idx in 0..left_leg_max_target {
        let which_set = uf.find(idx);
        if let Some(z) = set_to_part_num.get(&which_set) {
            left_to_pushout.push(*z);
        } else {
            set_to_part_num.insert(which_set, current_set_number);
            left_to_pushout.push(current_set_number);
            current_set_number += 1;
            representative.push(Left(idx));
        }
    }
    let mut right_to_pushout: Vec<MiddleIndex> = Vec::with_capacity(right_leg_max_target);
    for idx in 0..right_leg_max_target {
        let which_set = uf.find(idx + left_leg_max_target);
        if let Some(z) = set_to_part_num.get(&which_set) {
            right_to_pushout.push(*z);
        } else {
            set_to_part_num.insert(which_set, current_set_number);
            right_to_pushout.push(current_set_number);
            current_set_number += 1;
            representative.push(Right(idx));
        }
    }
    let pushout_target = current_set_number;
    Ok((
        pushout_target,
        left_to_pushout,
        right_to_pushout,
        representative,
    ))
}

mod test {
    #[test]
    fn empty_cospan() {
        use super::Cospan;
        let empty_cospan = Cospan::<u32>::new(vec![], vec![], vec![]);
        assert!(empty_cospan.left.len() == 0);
        assert!(empty_cospan.right.len() == 0);
        assert!(empty_cospan.middle.len() == 0);
    }

    #[test]
    fn left_only_cospan() {
        use super::Cospan;
        use either::{Left, Right};
        let mut my_cospan = Cospan::<u32>::new(vec![], vec![], vec![]);
        my_cospan.add_boundary_node(Left(Right(1)));
        my_cospan.add_boundary_node(Left(Right(2)));
        my_cospan.add_boundary_node(Left(Right(3)));
        my_cospan.add_boundary_node(Left(Left(1)));
        assert_eq!(my_cospan.left.len(), 4);
        assert_eq!(my_cospan.right.len(), 0);
        assert_eq!(my_cospan.middle.len(), 3);
        assert_eq!(my_cospan.left, vec![0, 1, 2, 1]);
    }

    #[test]
    fn ugly_cospan() {
        use super::Cospan;
        use crate::assert_ok;
        use either::{Left, Right};
        use petgraph::Graph;
        let mut my_cospan = Cospan::<bool>::new(vec![], vec![], vec![]);
        my_cospan.add_boundary_node(Right(Right(false)));
        my_cospan.add_boundary_node(Right(Right(true)));
        my_cospan.add_middle(true);
        my_cospan.add_boundary_node(Right(Right(true)));
        my_cospan.add_boundary_node(Right(Right(false)));
        my_cospan.add_boundary_node(Right(Left(4)));
        my_cospan.add_middle(true);
        my_cospan.add_boundary_node(Right(Right(true)));
        my_cospan.add_boundary_node(Left(Left(1)));
        my_cospan.add_boundary_node(Left(Left(2)));
        my_cospan.add_boundary_node(Left(Left(3)));
        my_cospan.add_boundary_node(Left(Left(3)));
        my_cospan.add_boundary_node(Left(Left(1)));
        my_cospan.add_boundary_node(Left(Left(2)));
        my_cospan.add_boundary_node(Left(Left(5)));
        my_cospan.add_boundary_node(Left(Left(3)));
        my_cospan.add_boundary_node(Left(Left(6)));
        let (_, _, _, _g): (_, _, _, Graph<bool, ()>) = my_cospan.to_graph(|z| (z, ()));
        let valid_info: Result<(), &'static str> = Ok(());
        assert_ok!(valid_info);
    }

    #[test]
    fn permutataion() {
        use super::Cospan;
        let my_cospan = Cospan::<()>::new(
            vec![0, 1, 2, 3, 4, 5, 6],
            vec![1, 0, 2, 3],
            vec![(), (), (), (), (), (), ()],
        );
        assert!(my_cospan.is_left_id);
        assert!(!my_cospan.is_right_id);
        let my_cospan2 =
            Cospan::<()>::new(vec![0, 1, 2, 3], vec![1, 0, 2, 3], vec![(), (), (), ()]);
        let res = my_cospan.compose(my_cospan2);
        match res {
            Ok(real_res) => {
                assert_eq!(real_res.left, vec![0, 1, 2, 3, 4, 5, 6]);
                assert_eq!(real_res.right, vec![0, 1, 2, 3]);
                assert_eq!(real_res.middle, vec![(), (), (), (), (), (), ()]);
            }
            Err(e) => {
                panic!("Could not compose simple example {:?}", e)
            }
        }
    }
}
