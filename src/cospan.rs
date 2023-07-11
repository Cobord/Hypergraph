use {
    crate::{
        category::{Composable, HasIdentity},
        finset::FinSetMap,
        monoidal::{GenericMonoidalInterpretable, Monoidal, MonoidalMorphism},
        symmetric_monoidal::SymmetricMonoidalMorphism,
        utils::{in_place_permute, represents_id, EitherExt},
    },
    either::Either::{self, Left, Right},
    log::warn,
    permutations::Permutation,
    petgraph::{
        prelude::Graph,
        stable_graph::{DefaultIx, NodeIndex},
    },
    std::{collections::HashMap, fmt::Debug},
    union_find::{UnionBySize, UnionFind},
};

type LeftIndex = usize;
type RightIndex = usize;
type MiddleIndex = usize;
type MiddleIndexOrLambda<Lambda> = Either<MiddleIndex, Lambda>;

#[derive(Clone)]
pub struct Cospan<Lambda: Sized + Eq + Copy + Debug> {
    left: Vec<MiddleIndex>, // the map from left (the domain side) nodes to the sink
    right: Vec<MiddleIndex>, // the map from right (the codomain side) nodes to the sink
    middle: Vec<Lambda>,    // the sink is a finite set with Lambda labels
    is_left_id: bool,
    is_right_id: bool,
}

impl<Lambda> Cospan<Lambda>
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
            let is_left_really_id = represents_id(self.left.iter().cloned());
            assert_eq!(
                is_left_really_id, self.is_left_id,
                "The identity nature of the left arrow was wrong"
            );
            let is_right_really_id = represents_id(self.right.iter().cloned());
            assert_eq!(
                is_right_really_id, self.is_right_id,
                "The identity nature of the right arrow was wrong"
            );
        }
    }

    pub fn new(left: Vec<MiddleIndex>, right: Vec<MiddleIndex>, middle: Vec<Lambda>) -> Self {
        let is_left_id = represents_id(left.iter().cloned());
        let is_right_id = represents_id(right.iter().cloned());
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
    pub fn empty() -> Self {
        Self::new(vec![], vec![], vec![])
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.left.is_empty() && self.right.is_empty() && self.middle.is_empty()
    }

    pub fn left_to_middle(&self) -> &[MiddleIndex] {
        &self.left
    }

    pub fn right_to_middle(&self) -> &[MiddleIndex] {
        &self.right
    }

    #[allow(dead_code)]
    pub fn add_boundary_node_known_target(
        &mut self,
        new_arrow: Either<MiddleIndex, MiddleIndex>,
    ) -> Either<LeftIndex, RightIndex> {
        /*
        add a new boundary node that maps to the specified middle index of new_arrow
        which side depends on whether new_arrow is Left/Right
        */
        self.add_boundary_node(new_arrow.bimap(|z| Left(z), |z| Left(z)))
    }

    #[allow(dead_code)]
    pub fn add_boundary_node_unknown_target(
        &mut self,
        new_arrow: Either<Lambda, Lambda>,
    ) -> Either<LeftIndex, RightIndex> {
        /*
        add a new boundary node that maps to a new middle node of specified label
        which side depends on whether new_arrow is Left/Right
        */
        self.add_boundary_node(new_arrow.bimap(|z| Right(z), |z| Right(z)))
    }

    pub fn add_boundary_node(
        &mut self,
        new_arrow: Either<MiddleIndexOrLambda<Lambda>, MiddleIndexOrLambda<Lambda>>,
    ) -> Either<LeftIndex, RightIndex> {
        /*
        add a new boundary node that maps to a new or existing middle node specified by new_arrow
        which side depends on whether new_arrow is Left/Right
        */
        match new_arrow {
            Left(tgt_info) => {
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
            }
            Right(tgt_info) => {
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
            }
        }
    }

    pub fn delete_boundary_node(&mut self, which_node: Either<LeftIndex, RightIndex>) {
        /*
        deletes a node from one side
        in this the sides are merely a Lambda labelled set
        so is ok to mix up the order of self.left/right
        */
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

    pub fn connect_pair(
        &mut self,
        node_1: Either<LeftIndex, RightIndex>,
        node_2: Either<LeftIndex, RightIndex>,
    ) {
        /*
        collapse the middle nodes that node_1 and node_2 connect to (A and B)
        into a single middle node with the same label as the shared label
        of A and B
        if A and B do not have the same label, give a warning and make no change
        */
        let mid_for_node_1 = match node_1 {
            Left(z) => self.left[z],
            Right(z) => self.right[z],
        };
        let mid_for_node_2 = match node_2 {
            Left(z) => self.left[z],
            Right(z) => self.right[z],
        };
        if mid_for_node_1 == mid_for_node_2 {
            return;
        }
        let type_ = self.middle[mid_for_node_1];
        if type_ != self.middle[mid_for_node_2] {
            warn!("Incompatible types. No change made.");
            return;
        }
        let _ = self.middle.swap_remove(mid_for_node_2);
        let old_last = self.middle.len();
        let last_removed = mid_for_node_2 == old_last;
        self.left.iter_mut().for_each(|v| {
            #[allow(clippy::needless_else)]
            if mid_for_node_2 == *v {
                *v = mid_for_node_1;
            } else if *v == old_last && !last_removed {
                *v = mid_for_node_2;
            } else {
            }
        });
        self.right.iter_mut().for_each(|v| {
            #[allow(clippy::needless_else)]
            if mid_for_node_2 == *v {
                *v = mid_for_node_1;
            } else if *v == old_last && !last_removed {
                *v = mid_for_node_2;
            } else {
            }
        });
    }

    pub fn add_middle(&mut self, new_middle: Lambda) -> MiddleIndex {
        /*
        add a new node to the sink with specified label
        */
        self.middle.push(new_middle);
        self.is_left_id = false;
        self.is_right_id = false;
        self.middle.len() - 1
    }

    pub fn map<F, Mu>(&self, f: F) -> Cospan<Mu>
    where
        F: Fn(Lambda) -> Mu,
        Mu: Sized + Eq + Copy + Debug,
    {
        /*
        change the labels with the function f
        */
        Cospan::new(
            self.left.clone(),
            self.right.clone(),
            self.middle.iter().map(|l| f(*l)).collect(),
        )
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
        /*
        make this into a graph
        vertices for every node in left,right and middle
        the vertices are colored by the first output of lambda_decorator based on their label
        the edges are colored by the second output of lambda_decorator
            based on the (shared) label of their endpoints
        */
        let mut graph = Graph::<T, U>::new();

        let all_middle_nodes: Vec<_> = self
            .middle
            .iter()
            .map(|mid| graph.add_node(lambda_decorator(*mid).0))
            .collect();

        let mut all_left_nodes = Vec::with_capacity(self.left.len());
        for cur_left_target in &self.left {
            let (node_dec, edge_dec) = lambda_decorator(self.middle[*cur_left_target]);
            let cur_left_node: NodeIndex<DefaultIx> = graph.add_node(node_dec);
            all_left_nodes.push(cur_left_node);
            graph.add_edge(cur_left_node, all_middle_nodes[*cur_left_target], edge_dec);
        }
        let mut all_right_nodes = Vec::with_capacity(self.right.len());
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

impl<Lambda> HasIdentity<Vec<Lambda>> for Cospan<Lambda>
where
    Lambda: Eq + Copy + Debug,
{
    fn identity(types: &Vec<Lambda>) -> Self {
        let num_types = types.len();
        Self {
            left: (0..num_types).collect(),
            right: (0..num_types).collect(),
            middle: types.to_vec(),
            is_left_id: true,
            is_right_id: true,
        }
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
    fn composable(&self, other: &Self) -> Result<(), String> {
        let self_interface = self.right.iter().map(|mid| self.middle[*mid]);
        let other_interface = other.left.iter().map(|mid| other.middle[*mid]);

        crate::utils::same_labels_check(self_interface, other_interface)
    }

    fn compose(&self, other: &Self) -> Result<Self, String> {
        self.composable(other)?;
        let (pushout_target, left_to_pushout, right_to_pushout, representative) =
            perform_pushout::<crate::QuickUnionUf<crate::UnionBySize>>(
                &self.right,
                self.middle.len(),
                self.is_right_id,
                &other.left,
                other.middle.len(),
                other.is_left_id,
            )?;
        let mut composition = Self::new(
            Vec::with_capacity(self.left.len()),
            Vec::with_capacity(other.right.len()),
            Vec::with_capacity(pushout_target),
        );
        for repr in representative {
            composition.add_middle(match repr {
                Left(z) => self.middle[z],
                Right(z) => other.middle[z],
            });
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

impl<Lambda> GenericMonoidalInterpretable<Lambda> for Cospan<Lambda> where Lambda: Eq + Copy + Debug {}

impl<Lambda> SymmetricMonoidalMorphism<Lambda> for Cospan<Lambda>
where
    Lambda: Eq + Sized + Copy + Debug,
{
    fn permute_side(&mut self, p: &Permutation, of_right_leg: bool) {
        in_place_permute(
            if of_right_leg {
                self.is_right_id = false;
                &mut self.right
            } else {
                self.is_left_id = false;
                &mut self.left
            },
            p,
        );
    }

    fn from_permutation(p: Permutation, types: &[Lambda], types_as_on_domain: bool) -> Self {
        let num_types = types.len();
        assert_eq!(p.len(), num_types);
        let id_temp = (0..num_types).collect::<Vec<usize>>();
        // inverses placed so that from(p1);from(p2) = from(p1;p2)
        //  left ; is cospan composition
        //  right ; is composition of permutation functions
        let p_underlying = if types_as_on_domain { p.inv() } else { p }.permute(&id_temp);
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
fn perform_pushout<T>(
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
    use crate::{
        category::{Composable, HasIdentity},
        monoidal::{Monoidal, MonoidalMorphism},
        symmetric_monoidal::SymmetricMonoidalMorphism,
    };

    #[test]
    fn empty_cospan() {
        use super::Cospan;
        let empty_cospan = Cospan::<u32>::empty();
        assert!(empty_cospan.is_empty());
    }

    #[test]
    fn left_only_cospan() {
        use super::Cospan;
        use either::{Left, Right};
        let mut cospan = Cospan::<u32>::empty();
        cospan.add_boundary_node(Left(Right(1)));
        cospan.add_boundary_node(Left(Right(2)));
        cospan.add_boundary_node(Left(Right(3)));
        cospan.add_boundary_node(Left(Left(1)));
        assert_eq!(cospan.left.len(), 4);
        assert_eq!(cospan.right.len(), 0);
        assert_eq!(cospan.middle.len(), 3);
        assert_eq!(cospan.left, vec![0, 1, 2, 1]);
        assert_eq!(cospan.middle, vec![1, 2, 3]);
    }

    #[test]
    fn ugly_cospan() {
        use super::Cospan;
        use either::{Left, Right};
        use petgraph::Graph;
        let mut cospan = Cospan::<bool>::empty();
        cospan.add_boundary_node(Right(Right(false)));
        cospan.add_boundary_node(Right(Right(true)));
        cospan.add_middle(true);
        cospan.add_boundary_node(Right(Right(true)));
        cospan.add_boundary_node(Right(Right(false)));
        cospan.add_boundary_node(Right(Left(4)));
        cospan.add_middle(true);
        cospan.add_boundary_node(Right(Right(true)));
        cospan.add_boundary_node(Left(Left(1)));
        cospan.add_boundary_node(Left(Left(2)));
        cospan.add_boundary_node(Left(Left(3)));
        cospan.add_boundary_node(Left(Left(3)));
        cospan.add_boundary_node(Left(Left(1)));
        cospan.add_boundary_node(Left(Left(2)));
        cospan.add_boundary_node(Left(Left(5)));
        cospan.add_boundary_node(Left(Left(3)));
        cospan.add_boundary_node(Left(Left(6)));
        let (_, _, _, _g): (_, _, _, Graph<bool, ()>) = cospan.to_graph(|z| (z, ()));
        assert_eq!(cospan.right.len(), 6);
        assert_eq!(cospan.right, vec![0, 1, 3, 4, 4, 6]);
        assert_eq!(cospan.left.len(), 9);
        assert_eq!(cospan.left, vec![1, 2, 3, 3, 1, 2, 5, 3, 6]);
        assert_eq!(
            cospan.middle,
            vec![false, true, true, true, false, true, true]
        );
    }

    #[test]
    fn permutatation_manual() {
        use super::Cospan;
        let whatever_types: Vec<_> = (0..5).map(|_| rand::random::<bool>()).collect();
        let mut full_types: Vec<bool> = vec![true, true];
        full_types.extend(whatever_types.clone());
        let cospan = Cospan::<bool>::new((0..=6).collect(), vec![1, 0, 2, 3], full_types);
        assert!(cospan.is_left_id);
        assert!(!cospan.is_right_id);
        let cospan2 = Cospan::<bool>::new(
            vec![0, 1, 2, 3],
            vec![1, 0, 2, 3],
            vec![true, true, whatever_types[0], whatever_types[1]],
        );
        let res = cospan.compose(&cospan2);
        let mut exp_middle = vec![true, true];
        exp_middle.extend(whatever_types.clone());
        match res {
            Ok(real_res) => {
                assert_eq!(real_res.left, (0..=6).collect::<Vec<_>>());
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
        enum Color {
            Red,
            Green,
            Blue,
        }
        let type_names_on_source = true;
        let cospan = Cospan::<Color>::from_permutation(
            Permutation::rotation_left(3, 1),
            &vec![Color::Red, Color::Green, Color::Blue],
            type_names_on_source,
        );
        let cospan_2 = Cospan::<Color>::from_permutation(
            Permutation::rotation_left(3, 2),
            &vec![Color::Blue, Color::Red, Color::Green],
            type_names_on_source,
        );
        let mid_interface_1 = cospan.codomain();
        let mid_interface_2 = cospan_2.domain();
        let comp = cospan.compose(&cospan_2);
        match comp {
            Ok(real_res) => {
                let expected_res = Cospan::identity(&vec![Color::Red, Color::Green, Color::Blue]);
                assert_eq!(expected_res.left, real_res.left);
                assert_eq!(expected_res.right, real_res.right);
                assert_eq!(expected_res.middle, real_res.middle);
            }
            Err(e) => {
                panic!(
                    "Could not compose simple example because {:?} did not match {:?}\n{:?}",
                    mid_interface_1, mid_interface_2, e
                );
            }
        }
        let type_names_on_source = false;
        let cospan = Cospan::<Color>::from_permutation(
            Permutation::rotation_left(3, 1),
            &vec![Color::Red, Color::Green, Color::Blue],
            type_names_on_source,
        );
        let cospan_2 = Cospan::<Color>::from_permutation(
            Permutation::rotation_left(3, 2),
            &vec![Color::Green, Color::Blue, Color::Red],
            type_names_on_source,
        );
        let mid_interface_1 = cospan.codomain();
        let mid_interface_2 = cospan_2.domain();
        let comp = cospan.compose(&cospan_2);
        match comp {
            Ok(real_res) => {
                let expected_res = Cospan::identity(&vec![Color::Green, Color::Blue, Color::Red]);
                assert_eq!(expected_res.left, real_res.left);
                assert_eq!(expected_res.right, real_res.right);
                assert_eq!(expected_res.middle, real_res.middle);
            }
            Err(e) => {
                panic!(
                    "Could not compose simple example because {:?} did not match {:?}\n{:?}",
                    mid_interface_1, mid_interface_2, e
                );
            }
        }
    }

    #[test]
    fn permutation_automatic() {
        use super::Cospan;
        use crate::utils::{in_place_permute, rand_perm};
        use rand::{distributions::Uniform, prelude::Distribution};
        let n_max = 10;
        let between = Uniform::<usize>::from(2..n_max);
        let mut rng = rand::thread_rng();
        let n = between.sample(&mut rng);
        let types_as_on_source = true;
        let p1 = rand_perm(n, n * 2);
        let p2 = rand_perm(n, n * 2);
        let prod = p1.clone() * p2.clone();
        let domain_types = (0..n).map(|idx| idx + 100).collect::<Vec<usize>>();
        let mut types_at_this_stage = domain_types.clone();
        let cospan_p1 = Cospan::from_permutation(p1.clone(), &domain_types, types_as_on_source);
        in_place_permute(&mut types_at_this_stage, &p1.inv());
        let cospan_p2 =
            Cospan::from_permutation(p2.clone(), &types_at_this_stage, types_as_on_source);
        in_place_permute(&mut types_at_this_stage, &p2.inv());
        let cospan_prod = cospan_p1.compose(&cospan_p2);
        match cospan_prod {
            Ok(real_res) => {
                let expected_res =
                    Cospan::from_permutation(prod, &domain_types, types_as_on_source);
                assert_eq!(real_res.left, expected_res.left);
                assert_eq!(real_res.right, expected_res.right);
                assert_eq!(real_res.middle, expected_res.middle);
                assert_eq!(real_res.domain(), domain_types);
                assert_eq!(real_res.codomain(), types_at_this_stage);
            }
            Err(e) => {
                panic!("Could not compose simple example\n{:?}", e)
            }
        }
        let types_as_on_source = false;
        let domain_types = (0..n).map(|idx| idx + 10).collect::<Vec<usize>>();
        let p1 = rand_perm(n, n * 2);
        let p2 = rand_perm(n, n * 2);
        let prod = p1.clone() * p2.clone();
        let mut types_at_this_stage = domain_types.clone();
        in_place_permute(&mut types_at_this_stage, &p1.inv());
        let cospan_p1 =
            Cospan::from_permutation(p1.clone(), &types_at_this_stage.clone(), types_as_on_source);
        in_place_permute(&mut types_at_this_stage, &p2.inv());
        let cospan_p2 =
            Cospan::from_permutation(p2.clone(), &types_at_this_stage, types_as_on_source);
        let cospan_prod = cospan_p1.compose(&cospan_p2);
        match cospan_prod {
            Ok(real_res) => {
                let expected_res =
                    Cospan::from_permutation(prod, &types_at_this_stage, types_as_on_source);
                assert_eq!(real_res.left, expected_res.left);
                assert_eq!(real_res.right, expected_res.right);
                assert_eq!(real_res.middle, expected_res.middle);
                assert_eq!(real_res.domain(), domain_types);
                assert_eq!(real_res.codomain(), types_at_this_stage);
            }
            Err(e) => {
                panic!("Could not compose simple example\n{:?}", e)
            }
        }
    }
}
