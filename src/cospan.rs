use either::Either::{self, Left, Right};
use permutations::Permutation;
use petgraph::{prelude::Graph, stable_graph::DefaultIx, stable_graph::NodeIndex};
use std::collections::HashMap;
use std::fmt::Debug;
use union_find::{UnionBySize, UnionFind};

use crate::category::Composable;
use crate::finset::FinSetMap;
use crate::monoidal::{Monoidal, MonoidalMorphism};
use crate::symmetric_monoidal::SymmetricMonoidalMorphism;
use crate::utils::{bimap, in_place_permute, represents_id};

type LeftIndex = usize;
type RightIndex = usize;
type MiddleIndex = usize;
type MiddleIndexOrLambda<Lambda> = Either<MiddleIndex, Lambda>;

#[derive(Clone)]
pub struct Cospan<Lambda: Sized + Eq + Copy + Debug> {
    left: Vec<MiddleIndex>,
    right: Vec<MiddleIndex>,
    middle: Vec<Lambda>,
    is_left_id: bool,
    is_right_id: bool,
}

impl<'a, Lambda> Cospan<Lambda>
where
    Lambda: Sized + Eq + Copy + Debug,
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

    #[allow(dead_code)]
    pub fn left_to_middle(&self) -> Vec<MiddleIndex> {
        self.left.clone()
    }
    #[allow(dead_code)]
    pub fn right_to_middle(&self) -> Vec<MiddleIndex> {
        self.right.clone()
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
}

impl<Lambda> Monoidal for Cospan<Lambda>
where
    Lambda: Eq + Sized + Copy + Debug,
{
    fn monoidal(&mut self, mut other: Self) {
        let middle_shift = self.middle.len();
        other.left.iter_mut().for_each(|v| *v += middle_shift);
        other.right.iter_mut().for_each(|v| *v += middle_shift);
        self.left.extend(other.left);
        self.right.extend(other.right);
        self.middle.extend(other.middle);
        self.is_left_id &= other.is_left_id;
        self.is_right_id &= other.is_right_id;
    }
}

impl<Lambda> Composable<Vec<Lambda>> for Cospan<Lambda>
where
    Lambda: Eq + Sized + Copy + Debug,
{
    fn compose(&self, other: &Self) -> Result<Self, String> {
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
                    return Err("Mismatch in cardinalities of common interface".to_string());
                }
                (None, Some(_)) => {
                    return Err("Mismatch in cardinalities of common interface".to_string());
                }
                (Some(w1), Some(w2)) => {
                    if w1 != w2 {
                        return Err(format!(
                            "Mismatch in labels of common interface. At some index there was {:?} vs {:?}",
                            w1, w2
                        ));
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
        for target_in_self_middle in &self.left {
            let target_in_pushout = left_to_pushout[*target_in_self_middle];
            composition.add_boundary_node(Left(Left(target_in_pushout)));
        }
        for target_in_other_middle in &other.right {
            let target_in_pushout = right_to_pushout[*target_in_other_middle];
            composition.add_boundary_node(Right(Left(target_in_pushout)));
        }
        Ok(composition)
    }

    fn domain(&self) -> Vec<Lambda> {
        self.left.iter().map(|mid| self.middle[*mid]).collect()
    }

    fn codomain(&self) -> Vec<Lambda> {
        self.right.iter().map(|mid| self.middle[*mid]).collect()
    }
}

impl<Lambda> MonoidalMorphism<Vec<Lambda>> for Cospan<Lambda> where Lambda: Eq + Sized + Copy + Debug
{}

impl<Lambda> SymmetricMonoidalMorphism<Vec<Lambda>> for Cospan<Lambda>
where
    Lambda: Eq + Sized + Copy + Debug,
{
    fn permute_side(&mut self, p: &Permutation, of_right_leg: bool) {
        if of_right_leg {
            self.is_right_id = false;
            in_place_permute(&mut self.right, p);
        } else {
            self.is_left_id = false;
            in_place_permute(&mut self.left, p);
        }
    }

    fn from_permutation(p: Permutation, types: &Vec<Lambda>, types_as_on_domain: bool) -> Self {
        let num_types = types.len();
        assert_eq!(p.len(), num_types);
        let id_temp = (0..num_types).collect::<Vec<usize>>();
        // inverses placed so that from(p1);from(p2) = from(p1;p2)
        //  left ; is cospan composition
        //  right ; is composition of permutation functions
        let p_underlying = if types_as_on_domain {
            p.inv().permute(&id_temp)
        } else {
            p.permute(&id_temp)
        };
        if types_as_on_domain {
            Self {
                left: (0..num_types).collect(),
                right: p_underlying,
                middle: types.to_vec(),
                is_left_id: true,
                is_right_id: false,
            }
        } else {
            Self {
                left: p_underlying,
                right: (0..num_types).collect(),
                middle: types.to_vec(),
                is_left_id: false,
                is_right_id: true,
            }
        }
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
    #[allow(unused_imports)]
    use crate::category::Composable;
    #[allow(unused_imports)]
    use crate::monoidal::{Monoidal, MonoidalMorphism};
    #[allow(unused_imports)]
    use crate::symmetric_monoidal::SymmetricMonoidalMorphism;

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
    fn permutatation_manual() {
        use super::Cospan;
        let whatever_types = (0..5)
            .map(|_| rand::random::<bool>())
            .collect::<Vec<bool>>();
        let mut full_types: Vec<bool> = vec![true, true];
        full_types.extend(whatever_types.clone());
        let my_cospan =
            Cospan::<bool>::new(vec![0, 1, 2, 3, 4, 5, 6], vec![1, 0, 2, 3], full_types);
        assert!(my_cospan.is_left_id);
        assert!(!my_cospan.is_right_id);
        let my_cospan2 = Cospan::<bool>::new(
            vec![0, 1, 2, 3],
            vec![1, 0, 2, 3],
            vec![true, true, whatever_types[0], whatever_types[1]],
        );
        let res = my_cospan.compose(&my_cospan2);
        let mut exp_middle = vec![true, true];
        exp_middle.extend(whatever_types.clone());
        match res {
            Ok(real_res) => {
                assert_eq!(real_res.left, vec![0, 1, 2, 3, 4, 5, 6]);
                assert_eq!(real_res.right, vec![0, 1, 2, 3]);
                assert_eq!(real_res.middle, exp_middle);
            }
            Err(e) => {
                panic!("Could not compose simple example\n{:?}", e)
            }
        }
    }

    #[test]
    fn permutatation_manual_labelled() {
        use super::Cospan;
        use permutations::Permutation;
        #[derive(Debug, PartialEq, Eq, Clone, Copy)]
        enum COLOR {
            RED,
            GREEN,
            BLUE,
        }
        let type_names_on_source = true;
        let my_cospan = Cospan::<COLOR>::from_permutation(
            Permutation::rotation_left(3, 1),
            &vec![COLOR::RED, COLOR::GREEN, COLOR::BLUE],
            type_names_on_source,
        );
        let my_cospan_2 = Cospan::<COLOR>::from_permutation(
            Permutation::rotation_left(3, 2),
            &vec![COLOR::BLUE, COLOR::RED, COLOR::GREEN],
            type_names_on_source,
        );
        let my_mid_interface_1 = my_cospan.codomain();
        let my_mid_interface_2 = my_cospan_2.domain();
        let comp = my_cospan.compose(&my_cospan_2);
        match comp {
            Ok(real_res) => {
                let expected_res = Cospan::identity(&vec![COLOR::RED, COLOR::GREEN, COLOR::BLUE]);
                assert_eq!(expected_res.left, real_res.left);
                assert_eq!(expected_res.right, real_res.right);
                assert_eq!(expected_res.middle, real_res.middle);
            }
            Err(e) => {
                panic!(
                    "Could not compose simple example because {:?} did not match {:?}\n{:?}",
                    my_mid_interface_1, my_mid_interface_2, e
                );
            }
        }
        let type_names_on_source = false;
        let my_cospan = Cospan::<COLOR>::from_permutation(
            Permutation::rotation_left(3, 1),
            &vec![COLOR::RED, COLOR::GREEN, COLOR::BLUE],
            type_names_on_source,
        );
        let my_cospan_2 = Cospan::<COLOR>::from_permutation(
            Permutation::rotation_left(3, 2),
            &vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED],
            type_names_on_source,
        );
        let my_mid_interface_1 = my_cospan.codomain();
        let my_mid_interface_2 = my_cospan_2.domain();
        let comp = my_cospan.compose(&my_cospan_2);
        match comp {
            Ok(real_res) => {
                let expected_res = Cospan::identity(&vec![COLOR::GREEN, COLOR::BLUE, COLOR::RED]);
                assert_eq!(expected_res.left, real_res.left);
                assert_eq!(expected_res.right, real_res.right);
                assert_eq!(expected_res.middle, real_res.middle);
            }
            Err(e) => {
                panic!(
                    "Could not compose simple example because {:?} did not match {:?}\n{:?}",
                    my_mid_interface_1, my_mid_interface_2, e
                );
            }
        }
    }

    #[test]
    fn permutatation_automatic() {
        use super::Cospan;
        use crate::utils::rand_perm;
        use rand::distributions::Uniform;
        use rand::prelude::Distribution;
        let n_max = 10;
        let between = Uniform::<usize>::from(2..n_max);
        let mut rng = rand::thread_rng();
        let my_n = between.sample(&mut rng);
        let types_as_on_source = true;
        let p1 = rand_perm(my_n, my_n * 2);
        let p2 = rand_perm(my_n, my_n * 2);
        let prod = p1.clone() * p2.clone();
        let cospan_p1 = Cospan::from_permutation(
            p1,
            &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
            types_as_on_source,
        );
        let cospan_p2 = Cospan::from_permutation(
            p2,
            &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
            types_as_on_source,
        );
        let cospan_prod = cospan_p1.compose(&cospan_p2);
        match cospan_prod {
            Ok(real_res) => {
                let expected_res = Cospan::from_permutation(
                    prod,
                    &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
                    types_as_on_source,
                );
                assert_eq!(real_res.left, expected_res.left);
                assert_eq!(real_res.right, expected_res.right);
                assert_eq!(real_res.middle, expected_res.middle);
            }
            Err(e) => {
                panic!("Could not compose simple example\n{:?}", e)
            }
        }
        let types_as_on_source = false;
        let p1 = rand_perm(my_n, my_n * 2);
        let p2 = rand_perm(my_n, my_n * 2);
        let prod = p1.clone() * p2.clone();
        let cospan_p1 = Cospan::from_permutation(
            p1,
            &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
            types_as_on_source,
        );
        let cospan_p2 = Cospan::from_permutation(
            p2,
            &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
            types_as_on_source,
        );
        let cospan_prod = cospan_p1.compose(&cospan_p2);
        match cospan_prod {
            Ok(real_res) => {
                let expected_res = Cospan::from_permutation(
                    prod,
                    &(0..my_n).map(|_| ()).collect::<Vec<()>>(),
                    types_as_on_source,
                );
                assert_eq!(real_res.left, expected_res.left);
                assert_eq!(real_res.right, expected_res.right);
                assert_eq!(real_res.middle, expected_res.middle);
            }
            Err(e) => {
                panic!("Could not compose simple example\n{:?}", e)
            }
        }
    }
}
