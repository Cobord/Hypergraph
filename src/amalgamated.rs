use std::{
    collections::VecDeque,
    ops::{Div, DivAssign, Mul, MulAssign},
};

use either::Either::{self, Left, Right};
use num::One;

use crate::fp_gp::FinitelyPresentedGroup;

pub trait SimpleAmalgamater<G1, G2> {
    fn swapper(&self, x: &G2, y: &G1) -> Option<(G1, G2, G1, G2)>;
    /*
    the only relations in the amalgamation are of the form
    b_1 a_1 = a_2 b_2 a_3 b_3
    with the latter being the preferred form
    for subsequent reference this will be denoted as G1 *_{AM} G2
    */
}

#[allow(dead_code)]
#[derive(PartialEq, Eq, Clone)]
pub enum FewAssum<G1, G2> {
    Free,
    SomeCommuting(fn(&G1, &G2) -> bool),
    ResourceBasedCommuting(fn(Either<&G1, &G2>) -> Vec<usize>),
}

impl<G1, G2> SimpleAmalgamater<G1, G2> for FewAssum<G1, G2>
where
    G1: One + Clone,
    G2: One + Clone,
{
    fn swapper(&self, x: &G2, y: &G1) -> Option<(G1, G2, G1, G2)> {
        match self {
            FewAssum::Free => None,
            FewAssum::SomeCommuting(do_commute) => {
                if do_commute(y, x) {
                    Some((y.clone(), x.clone(), G1::one(), G2::one()))
                } else {
                    None
                }
            }
            FewAssum::ResourceBasedCommuting(which_resources_used) => {
                let x_used = which_resources_used(Right(x));
                let mut y_used = which_resources_used(Left(y));
                y_used.sort();
                let disjoint = !x_used
                    .into_iter()
                    .any(|x_cur| y_used.binary_search(&x_cur).is_ok());
                if disjoint {
                    Some((y.clone(), x.clone(), G1::one(), G2::one()))
                } else {
                    None
                }
            }
        }
    }
}

#[allow(dead_code)]
#[derive(PartialEq, Eq, Clone)]
pub enum FreeMonoidy<X1, X2> {
    SomeCommuting(fn(&X1, &X2) -> bool),
    ResourceBasedCommuting(fn(Either<&X1, &X2>) -> Vec<usize>),
}

impl<G1, G2, X1, X2> SimpleAmalgamater<G1, G2> for FreeMonoidy<X1, X2>
where
    G1: Clone + From<VecDeque<X1>> + Into<VecDeque<X1>>,
    G2: Clone + From<VecDeque<X2>> + Into<VecDeque<X2>>,
{
    fn swapper(&self, x: &G2, y: &G1) -> Option<(G1, G2, G1, G2)> {
        /*
        TODO : fix repetition
        */
        match self {
            FreeMonoidy::SomeCommuting(do_commute) => {
                let mut found_change_at_all = false;
                let mut ret_val_vecs_1: VecDeque<X2> = x.clone().into();
                let mut ret_val_vecs_2: VecDeque<X1> = y.clone().into();
                let x_len = ret_val_vecs_1.len();
                let y_len = ret_val_vecs_2.len();
                let mut ret_val_vecs_0: VecDeque<X1> = VecDeque::with_capacity(y_len / 2);
                let mut ret_val_vecs_3: VecDeque<X2> = VecDeque::with_capacity(x_len / 2);
                for _ in 0..std::cmp::min(x_len, y_len) {
                    let mut found_change_now = false;
                    if let Some(last_of_1) = ret_val_vecs_1.pop_back() {
                        if ret_val_vecs_2
                            .iter()
                            .all(|in_2| do_commute(in_2, &last_of_1))
                        {
                            ret_val_vecs_3.push_front(last_of_1);
                            found_change_now = true;
                        } else {
                            ret_val_vecs_1.push_back(last_of_1);
                        }
                    } else if !ret_val_vecs_2.is_empty() {
                        found_change_now = true;
                        ret_val_vecs_0.append(&mut ret_val_vecs_2);
                    }
                    if let Some(first_of_2) = ret_val_vecs_2.pop_front() {
                        if ret_val_vecs_1
                            .iter()
                            .all(|in_1| do_commute(&first_of_2, in_1))
                        {
                            ret_val_vecs_0.push_back(first_of_2);
                            found_change_now = true;
                        } else {
                            ret_val_vecs_2.push_front(first_of_2);
                        }
                    } else if !ret_val_vecs_1.is_empty() {
                        found_change_now = true;
                        ret_val_vecs_1.append(&mut ret_val_vecs_3);
                        std::mem::swap(&mut ret_val_vecs_1, &mut ret_val_vecs_3);
                    }
                    if found_change_now {
                        found_change_at_all = true;
                    } else {
                        break;
                    }
                }
                if found_change_at_all {
                    let ret_val = (
                        ret_val_vecs_0.into(),
                        ret_val_vecs_1.into(),
                        ret_val_vecs_2.into(),
                        ret_val_vecs_3.into(),
                    );
                    Some(ret_val)
                } else {
                    None
                }
            }
            FreeMonoidy::ResourceBasedCommuting(which_resources_used) => {
                let do_commute = |x1: &X1, x2: &X2| {
                    let x_used = which_resources_used(Left(x1));
                    let mut y_used = which_resources_used(Right(x2));
                    y_used.sort();
                    !x_used
                        .into_iter()
                        .any(|x_cur| y_used.binary_search(&x_cur).is_ok())
                };
                let mut found_change_at_all = false;
                let mut ret_val_vecs_1: VecDeque<X2> = x.clone().into();
                let mut ret_val_vecs_2: VecDeque<X1> = y.clone().into();
                let x_len = ret_val_vecs_1.len();
                let y_len = ret_val_vecs_2.len();
                let mut ret_val_vecs_0: VecDeque<X1> = VecDeque::with_capacity(y_len / 2);
                let mut ret_val_vecs_3: VecDeque<X2> = VecDeque::with_capacity(x_len / 2);
                for _ in 0..std::cmp::min(x_len, y_len) {
                    let mut found_change_now = false;
                    if let Some(last_of_1) = ret_val_vecs_1.pop_back() {
                        if ret_val_vecs_2
                            .iter()
                            .all(|in_2| do_commute(in_2, &last_of_1))
                        {
                            ret_val_vecs_3.push_front(last_of_1);
                            found_change_now = true;
                        } else {
                            ret_val_vecs_1.push_back(last_of_1);
                        }
                    } else if !ret_val_vecs_2.is_empty() {
                        found_change_now = true;
                        ret_val_vecs_0.append(&mut ret_val_vecs_2);
                    }
                    if let Some(first_of_2) = ret_val_vecs_2.pop_front() {
                        if ret_val_vecs_1
                            .iter()
                            .all(|in_1| do_commute(&first_of_2, in_1))
                        {
                            ret_val_vecs_0.push_back(first_of_2);
                            found_change_now = true;
                        } else {
                            ret_val_vecs_2.push_front(first_of_2);
                        }
                    } else if !ret_val_vecs_1.is_empty() {
                        found_change_now = true;
                        ret_val_vecs_1.append(&mut ret_val_vecs_3);
                        std::mem::swap(&mut ret_val_vecs_1, &mut ret_val_vecs_3);
                    }
                    if found_change_now {
                        found_change_at_all = true;
                    } else {
                        break;
                    }
                }
                if found_change_at_all {
                    let ret_val = (
                        ret_val_vecs_0.into(),
                        ret_val_vecs_1.into(),
                        ret_val_vecs_2.into(),
                        ret_val_vecs_3.into(),
                    );
                    Some(ret_val)
                } else {
                    None
                }
            }
        }
    }
}

#[derive(PartialEq, Eq, Clone)]
pub struct SimplyAmalgamatedProduct<G1, G2, SimpAmal>
where
    G1: MulAssign + Eq + Clone,
    G2: MulAssign + Eq + Clone,
    SimpAmal: SimpleAmalgamater<G1, G2> + Eq + Clone,
{
    pieces: Vec<(G1, G2)>,
    my_am: SimpAmal,
}

impl<G1, G2, SimpAmal> SimplyAmalgamatedProduct<G1, G2, SimpAmal>
where
    G1: MulAssign + Eq + Clone,
    G2: MulAssign + Eq + Clone,
    SimpAmal: SimpleAmalgamater<G1, G2> + Eq + Clone,
{
    pub fn make_one(my_am: SimpAmal) -> Self {
        /*
        the One trait but need to be able to input my_am
        */
        Self {
            pieces: vec![],
            my_am,
        }
    }

    #[allow(dead_code)]
    pub fn convert_to_g3<G3: One>(
        &self,
        g1_into: impl Fn(&G1) -> G3,
        g2_into: impl Fn(&G2) -> G3,
    ) -> G3 {
        /*
        convert to another monoid G3 based on how G1 and G2 parts get converted
        */
        self.pieces
            .iter()
            .fold(G3::one(), |acc, (g1_part, g2_part)| {
                acc * g1_into(g1_part) * g2_into(g2_part)
            })
    }

    #[allow(dead_code)]
    fn convert_into_iterator<X1, X2>(self) -> impl Iterator<Item = Either<X1, X2>>
    where
        G1: IntoIterator<Item = X1>,
        G2: IntoIterator<Item = X2>,
    {
        /*
        each G1,G2 piece monoid is a equivalent to a sequence in the letters X1 and X2
        respectively
        so this G1 *_AM G2 gives a sequence in Either<X1,X2>
        */
        self.pieces.into_iter().flat_map(|(g1_piece, g2_piece)| {
            g1_piece
                .into_iter()
                .map(Left)
                .chain(g2_piece.into_iter().map(Right))
        })
    }

    #[allow(dead_code)]
    pub fn right_act<X>(
        &self,
        g1_right_act: impl Fn(&G1, &mut X),
        g2_right_act: impl Fn(&G2, &mut X),
        target_point: &mut X,
    ) {
        /*
        if G1 and G2 both act on X
        in a way that the cross relations hold
        these laws are not enforced
        the caller is responsible for passing in correct gi_right_act functions
        then self does too
        */
        self.pieces.iter().rev().for_each(|(g1_part, g2_part)| {
            g2_right_act(g2_part, target_point);
            g1_right_act(g1_part, target_point);
        });
    }
}

impl<G1, G2, SimpAmal> SimplyAmalgamatedProduct<G1, G2, SimpAmal>
where
    G1: One + MulAssign + Eq + Clone,
    G2: One + MulAssign + Eq + Clone,
    SimpAmal: SimpleAmalgamater<G1, G2> + Eq + Clone,
{
    #[allow(dead_code)]
    pub fn new(some_pieces: Vec<Either<(G1, G2), Either<G1, G2>>>, am_to_use: SimpAmal) -> Self {
        /*
        create a new G1 *_{AM} G2 group element
        the entries of the vector can be (G1,G2) pairs like they are in self.pieces
        or they can be either g1 g2 for a single part of the tuple
        the either is inside the vec so they can be heterogeneous
        */
        let mut ret_val = Self::make_one(am_to_use);
        for cur_piece in some_pieces.into_iter() {
            match cur_piece {
                Left(both_together) => {
                    ret_val *= Left(both_together.0);
                    ret_val *= Right(both_together.1);
                }
                Right(one_at_time) => {
                    ret_val *= one_at_time;
                }
            }
        }
        ret_val
    }

    #[allow(dead_code)]
    pub fn into_free_version(self) -> SimplyAmalgamatedProduct<G1, G2, FewAssum<G1, G2>> {
        /*
        forget the relations that self.my_am would impose
        */
        SimplyAmalgamatedProduct::<G1, G2, FewAssum<G1, G2>> {
            pieces: self.pieces,
            my_am: FewAssum::Free,
        }
    }

    #[allow(dead_code)]
    pub fn from_free_version(
        free_version: SimplyAmalgamatedProduct<G1, G2, FewAssum<G1, G2>>,
        am_to_use: SimpAmal,
    ) -> Self {
        /*
        go from a free word alternating in G1 and G2 to the corresponding
        element in G1 *_AM G2
        */
        assert!(free_version.my_am == FewAssum::Free);
        let mut to_ret = Self {
            pieces: free_version.pieces,
            my_am: am_to_use,
        };
        let _ = to_ret.simplify(None);
        to_ret
    }

    pub fn simplify(&mut self, idcs_to_look: Option<Vec<usize>>) -> bool {
        /*
        simplify the presentation according to the rules of self.my_am.swapper
        if now the only place a change will happen are among a small set of options
        can pass that in as idcs_to_look, otherwise use None there
        return whether any such simplification occurred
        */
        if self.pieces.is_empty() {
            return false;
        }
        let mut changed = false;
        let mut real_idcs = idcs_to_look.unwrap_or((0..self.pieces.len() - 1).collect());
        let len_self_pieces = self.pieces.len();
        let keep_adding_to_look = 2 * len_self_pieces;
        let additional = std::cmp::max(real_idcs.len(), len_self_pieces / 8);
        real_idcs.reserve(additional);
        let mut iter_num = 0;
        let g1_one = G1::one();
        let g2_one = G2::one();
        while let Some(cur_idx) = real_idcs.pop() {
            if cur_idx >= len_self_pieces - 1 {
                continue;
            }
            iter_num += 1;
            let (g1, g2) = &self.pieces[cur_idx];
            let (g3, g4) = &self.pieces[cur_idx + 1];
            if *g3 == g1_one && *g4 == g2_one {
            } else if *g2 == g2_one || *g3 == g1_one {
                let g13 = g1.clone() * g3.clone();
                let g24 = g2.clone() * g4.clone();
                let new_piece_nonident = g13 != g1_one || g24 != g2_one;
                changed = true;
                self.pieces[cur_idx] = (g13, g24);
                self.pieces[cur_idx + 1] = (g1_one.clone(), g2_one.clone());
                if iter_num <= keep_adding_to_look {
                    if cur_idx > 0 && new_piece_nonident {
                        real_idcs.push(cur_idx - 1);
                    }
                    if cur_idx + 2 < len_self_pieces {
                        real_idcs.push(cur_idx + 1);
                    }
                }
            } else if let Some((h1, h2, h3, h4)) = self.my_am.swapper(g2, g3) {
                let g1_clone = g1.clone();
                let g4_clone = g4.clone();
                let cur_idx_again = h2 == g2_one || h3 == g1_one;
                changed = true;
                self.pieces[cur_idx] = (g1_clone * h1, h2);
                self.pieces[cur_idx + 1] = (h3, h4 * g4_clone);
                if iter_num <= keep_adding_to_look {
                    if cur_idx > 0 {
                        real_idcs.push(cur_idx - 1);
                    }
                    if cur_idx + 2 < len_self_pieces {
                        real_idcs.push(cur_idx + 1);
                    }
                    if cur_idx_again {
                        real_idcs.push(cur_idx);
                    }
                }
            }
        }
        self.pieces.retain(|(g1, g2)| {
            let g1_id = *g1 == g1_one;
            let g2_id = *g2 == g2_one;
            !(g1_id && g2_id)
        });
        if changed {
            true
        } else {
            self.pieces.len() < len_self_pieces
        }
    }
}

impl<G1, G2, SimpAmal> MulAssign for SimplyAmalgamatedProduct<G1, G2, SimpAmal>
where
    G1: One + MulAssign + Eq + Clone,
    G2: One + MulAssign + Eq + Clone,
    SimpAmal: SimpleAmalgamater<G1, G2> + Eq + Clone,
{
    fn mul_assign(&mut self, rhs: Self) {
        if self.pieces.is_empty() {
            self.pieces.extend(rhs.pieces);
            return;
        }
        #[allow(clippy::suspicious_op_assign_impl)]
        let len_before_m1 = self.pieces.len() - 1;
        self.pieces.extend(rhs.pieces);
        let _ = self.simplify(Some(vec![len_before_m1]));
    }
}

impl<G1, G2, SimpAmal> MulAssign<Either<G1, G2>> for SimplyAmalgamatedProduct<G1, G2, SimpAmal>
where
    G1: One + MulAssign + Eq + Clone,
    G2: One + MulAssign + Eq + Clone,
    SimpAmal: SimpleAmalgamater<G1, G2> + Eq + Clone,
{
    fn mul_assign(&mut self, rhs: Either<G1, G2>) {
        let (g1_part, g2_part) = match rhs {
            Left(only_g1) => (only_g1, G2::one()),
            Right(only_g2) => (G1::one(), only_g2),
        };
        let rhs_embedded = Self {
            pieces: vec![(g1_part, g2_part)],
            my_am: self.my_am.clone(),
        };
        self.mul_assign(rhs_embedded);
    }
}

impl<G1, G2, SimpAmal> Mul for SimplyAmalgamatedProduct<G1, G2, SimpAmal>
where
    G1: One + MulAssign + Eq + Clone,
    G2: One + MulAssign + Eq + Clone,
    SimpAmal: SimpleAmalgamater<G1, G2> + Eq + Clone,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        assert!(self.my_am == rhs.my_am);
        if self.pieces.is_empty() {
            return rhs;
        }
        let len_before_m1 = self.pieces.len() - 1;
        let mut new_pieces = Vec::with_capacity(self.pieces.len() + rhs.pieces.len());
        new_pieces.extend(self.pieces);
        new_pieces.extend(rhs.pieces);
        let mut ret_val = Self {
            pieces: new_pieces,
            my_am: self.my_am.clone(),
        };
        let _ = ret_val.simplify(Some(vec![len_before_m1]));
        ret_val
    }
}

impl<G1, G2> One for SimplyAmalgamatedProduct<G1, G2, FewAssum<G1, G2>>
where
    G1: One + MulAssign + Eq + Clone,
    G2: One + MulAssign + Eq + Clone,
{
    fn one() -> Self {
        Self {
            pieces: vec![],
            my_am: FewAssum::Free,
        }
    }
}

impl<G1, G2, SimpAmal> DivAssign for SimplyAmalgamatedProduct<G1, G2, SimpAmal>
where
    G1: One + MulAssign + Eq + Clone + DivAssign,
    G2: One + MulAssign + Eq + Clone + DivAssign,
    SimpAmal: SimpleAmalgamater<G1, G2> + Eq + Clone,
{
    fn div_assign(&mut self, rhs: Self) {
        assert!(self.my_am == rhs.my_am);
        if rhs.pieces.is_empty() {
            return;
        }
        let rhs_one = Self::make_one(rhs.my_am.clone());
        let mut rhs_inv = Self::make_one(rhs.my_am.clone());
        for (g1_part, g2_part) in rhs.pieces.iter().rev() {
            let mut g12_inv = rhs_one.clone();
            let mut g1_inv = G1::one();
            g1_inv /= g1_part.clone();
            let mut g2_inv = G2::one();
            g2_inv /= g2_part.clone();
            g12_inv *= Right(g2_inv);
            g12_inv *= Left(g1_inv);
            rhs_inv *= g12_inv;
        }
        *self *= rhs_inv;
    }
}

impl<G1, G2, SimpAmal> Div for SimplyAmalgamatedProduct<G1, G2, SimpAmal>
where
    G1: One + MulAssign + Eq + Clone + DivAssign,
    G2: One + MulAssign + Eq + Clone + DivAssign,
    SimpAmal: SimpleAmalgamater<G1, G2> + Eq + Clone,
{
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        assert!(self.my_am == rhs.my_am);
        let mut ret_val = self.clone();
        ret_val *= self;
        ret_val /= rhs;
        ret_val
    }
}

impl<G1, G2> FinitelyPresentedGroup for SimplyAmalgamatedProduct<G1, G2, FewAssum<G1, G2>>
where
    G1: FinitelyPresentedGroup + Eq + Clone,
    G2: FinitelyPresentedGroup + Eq + Clone,
{
    fn generator(n: usize) -> Self {
        let g1_count = G1::num_generators();
        let g2_count = G2::num_generators();
        let n_mod = n % (g1_count + g2_count);
        if n_mod < g1_count {
            let piece = G1::generator(n_mod);
            Self {
                pieces: vec![(piece, G2::one())],
                my_am: FewAssum::Free,
            }
        } else {
            let piece = G2::generator(n_mod - g1_count);
            Self {
                pieces: vec![(G1::one(), piece)],
                my_am: FewAssum::Free,
            }
        }
    }

    fn num_generators() -> usize {
        G1::num_generators() + G2::num_generators()
    }
}

struct AlternatingSimplifier<G1, G2, G3, G4, SimpAmal1, SimpAmal2, G5Letters>
where
    G1: MulAssign + Eq + Clone + Into<Vec<G5Letters>>,
    G2: MulAssign + Eq + Clone + Into<Vec<G5Letters>>,
    SimpAmal1: SimpleAmalgamater<G1, G2> + Eq + Clone,
    G3: MulAssign + Eq + Clone + Into<Vec<G5Letters>>,
    G4: MulAssign + Eq + Clone + Into<Vec<G5Letters>>,
    SimpAmal2: SimpleAmalgamater<G3, G4> + Eq + Clone,
    G5Letters: Into<Either<G1, G2>> + Into<Either<G3, G4>>,
{
    done_left: bool,
    done_right: bool,
    cur_word: Vec<G5Letters>,
    g1g2_iden: SimplyAmalgamatedProduct<G1, G2, SimpAmal1>,
    g3g4_iden: SimplyAmalgamatedProduct<G3, G4, SimpAmal2>,
}

impl<G1, G2, G3, G4, SimpAmal1, SimpAmal2, G5Letters>
    AlternatingSimplifier<G1, G2, G3, G4, SimpAmal1, SimpAmal2, G5Letters>
where
    G1: One + MulAssign + Eq + Clone + Into<Vec<G5Letters>>,
    G2: One + MulAssign + Eq + Clone + Into<Vec<G5Letters>>,
    SimpAmal1: SimpleAmalgamater<G1, G2> + Eq + Clone,
    G3: One + MulAssign + Eq + Clone + Into<Vec<G5Letters>>,
    G4: One + MulAssign + Eq + Clone + Into<Vec<G5Letters>>,
    SimpAmal2: SimpleAmalgamater<G3, G4> + Eq + Clone,
    G5Letters: Into<Either<G1, G2>> + Into<Either<G3, G4>> + Eq + Clone,
{
    pub fn new(cur_word: &[G5Letters], amal_1: SimpAmal1, amal_2: SimpAmal2) -> Self {
        let g1g2_iden = SimplyAmalgamatedProduct::<G1, G2, SimpAmal1>::make_one(amal_1);
        let g3g4_iden = SimplyAmalgamatedProduct::<G3, G4, SimpAmal2>::make_one(amal_2);
        Self {
            done_left: false,
            done_right: false,
            cur_word: cur_word.to_vec(),
            g1g2_iden,
            g3g4_iden,
        }
    }

    pub fn alternating_simplify(&mut self, effort_cutoff: usize, max_word_length: usize) {
        let mut iters_used_up = 0;
        let mut done = false;
        while !done && iters_used_up < effort_cutoff {
            let iters_used_up_more;
            (done, iters_used_up_more) =
                self.run_back_and_forth(effort_cutoff - iters_used_up, max_word_length);
            iters_used_up += iters_used_up_more + 1;
        }
    }

    fn run_back_and_forth(&mut self, max_iter: usize, max_word_length: usize) -> (bool, usize) {
        if max_iter == 0 {
            return (false, 0);
        }
        if self.cur_word.len() > max_word_length {
            let mut new_word = Vec::with_capacity(self.cur_word.len());
            let num_chunks = self.cur_word.len() / max_word_length + 1;
            let max_iter_chunky = std::cmp::min(max_iter / num_chunks, 1);
            let mut count_iters_used = 0;
            for chunk in self.cur_word.chunks(max_word_length) {
                let mut chunk_self = Self::new(
                    chunk,
                    self.g1g2_iden.my_am.clone(),
                    self.g3g4_iden.my_am.clone(),
                );
                let (_, chunk_used) =
                    chunk_self.run_back_and_forth(max_iter_chunky, max_word_length);
                count_iters_used += chunk_used;
                new_word.extend(chunk_self.cur_word);
            }
            self.cur_word = new_word;
            return (false, count_iters_used);
        }
        for iters_used in 0..max_iter {
            if self.done_left && self.done_right {
                return (true, iters_used);
            }
            self.do_left();
            self.do_right();
        }
        (false, max_iter)
    }

    fn do_left(&mut self) {
        if self.done_left {
            return;
        }
        let mut as_g1g2 = self.g1g2_iden.clone();
        for cur_letter in &self.cur_word {
            let either_g1g2_cur: Either<G1, G2> = cur_letter.clone().into();
            as_g1g2 *= either_g1g2_cur;
        }
        let new_word: Vec<G5Letters> = as_g1g2
            .pieces
            .into_iter()
            .flat_map(|(g1_part, g2_part)| {
                let g5_vec_first: Vec<G5Letters> = g1_part.into();
                let g5_vec_second: Vec<G5Letters> = g2_part.into();
                let mut to_ret = Vec::with_capacity(g5_vec_first.len() + (g5_vec_second.len()));
                to_ret.extend(g5_vec_first);
                to_ret.extend(g5_vec_second);
                to_ret
            })
            .collect();
        self.done_left = true;
        if new_word == self.cur_word {
            return;
        }
        self.cur_word = new_word;
        self.done_right = false;
    }

    fn do_right(&mut self) {
        if self.done_right {
            return;
        }
        let mut as_g3g4 = self.g3g4_iden.clone();
        for cur_letter in &self.cur_word {
            let either_g3g4_cur: Either<G3, G4> = cur_letter.clone().into();
            as_g3g4 *= either_g3g4_cur;
        }
        let new_word: Vec<G5Letters> = as_g3g4
            .pieces
            .into_iter()
            .flat_map(|(g3_part, g4_part)| {
                let g5_vec_first: Vec<G5Letters> = g3_part.into();
                let g5_vec_second: Vec<G5Letters> = g4_part.into();
                let mut to_ret = Vec::with_capacity(g5_vec_first.len() + (g5_vec_second.len()));
                to_ret.extend(g5_vec_first);
                to_ret.extend(g5_vec_second);
                to_ret
            })
            .collect();
        self.done_right = true;
        if new_word == self.cur_word {
            return;
        }
        self.cur_word = new_word;
        self.done_left = false;
    }
}

#[repr(transparent)]
struct NonAlternatingSimplifier<G1, G2, SimpAmal1, G3Letters>
where
    G1: One + MulAssign + Eq + Clone + Into<Vec<G3Letters>>,
    G2: One + MulAssign + Eq + Clone + Into<Vec<G3Letters>>,
    SimpAmal1: SimpleAmalgamater<G1, G2> + Eq + Clone,
    G3Letters: Into<Either<G1, G2>> + Eq + Clone,
{
    underlying: AlternatingSimplifier<G1, G2, G1, G2, SimpAmal1, SimpAmal1, G3Letters>,
}

impl<G1, G2, SimpAmal1, G3Letters> NonAlternatingSimplifier<G1, G2, SimpAmal1, G3Letters>
where
    G1: One + MulAssign + Eq + Clone + Into<Vec<G3Letters>>,
    G2: One + MulAssign + Eq + Clone + Into<Vec<G3Letters>>,
    SimpAmal1: SimpleAmalgamater<G1, G2> + Eq + Clone,
    G3Letters: Into<Either<G1, G2>> + Eq + Clone,
{
    #[allow(dead_code)]
    pub fn new(cur_word: &[G3Letters], amal_1: SimpAmal1) -> Self {
        Self {
            underlying:
                AlternatingSimplifier::<G1, G2, G1, G2, SimpAmal1, SimpAmal1, G3Letters>::new(
                    cur_word,
                    amal_1.clone(),
                    amal_1,
                ),
        }
    }

    #[allow(dead_code)]
    pub fn simplify(&mut self, effort_cutoff: usize, max_word_length: usize) {
        // does 1 unnecessary round of do_right
        // but that should create no additional simplifications
        self.underlying
            .alternating_simplify(effort_cutoff, max_word_length);
    }
}

mod test_setup {
    use num::One;
    use std::ops::{DivAssign, Mul, MulAssign};

    use crate::fp_gp::FinitelyPresentedGroup;

    #[derive(PartialEq, Eq, Clone, Debug)]
    pub struct Z2Part(pub bool);
    impl MulAssign for Z2Part {
        #[allow(clippy::suspicious_op_assign_impl)]
        fn mul_assign(&mut self, rhs: Self) {
            self.0 ^= rhs.0;
        }
    }
    impl DivAssign for Z2Part {
        #[allow(clippy::suspicious_op_assign_impl)]
        fn div_assign(&mut self, rhs: Self) {
            self.0 ^= rhs.0;
        }
    }
    impl Mul for Z2Part {
        type Output = Self;

        #[allow(clippy::suspicious_arithmetic_impl)]
        fn mul(self, rhs: Self) -> Self::Output {
            Self(self.0 ^ rhs.0)
        }
    }
    impl One for Z2Part {
        fn one() -> Self {
            Self(false)
        }
    }

    impl FinitelyPresentedGroup for Z2Part {
        fn generator(_n: usize) -> Self {
            Self(true)
        }

        fn num_generators() -> usize {
            1
        }
    }
    #[allow(dead_code)]
    pub fn s_action(me: &Z2Part, fraction: &mut (i128, i128)) {
        if me.0 {
            let temp = fraction.0;
            fraction.0 = -fraction.1;
            fraction.1 = temp;
        }
    }

    #[repr(u8)]
    #[derive(PartialEq, Eq, Clone, Copy, Debug)]
    #[allow(clippy::enum_variant_names)]
    pub enum Z3Part {
        STZero = 0,
        STOne = 1,
        STTwo = 2,
    }
    impl MulAssign for Z3Part {
        fn mul_assign(&mut self, rhs: Self) {
            let self_num = *self as u8;
            let rhs_num = rhs as u8;
            let new_self_num = (self_num + rhs_num) % 3;
            if new_self_num == 0 {
                *self = Self::STZero;
            } else if new_self_num == 1 {
                *self = Self::STOne;
            } else {
                *self = Self::STTwo
            }
        }
    }
    impl DivAssign for Z3Part {
        #[allow(clippy::suspicious_op_assign_impl)]
        fn div_assign(&mut self, rhs: Self) {
            let rhs_inv = match rhs {
                Z3Part::STZero => Z3Part::STZero,
                Z3Part::STOne => Z3Part::STTwo,
                Z3Part::STTwo => Z3Part::STOne,
            };
            *self *= rhs_inv;
        }
    }
    impl Mul for Z3Part {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self::Output {
            let mut ret_val = Self::STZero;
            ret_val *= self;
            ret_val *= rhs;
            ret_val
        }
    }
    impl One for Z3Part {
        fn one() -> Self {
            Self::STZero
        }
    }
    #[allow(dead_code)]
    pub fn st_action(me: &Z3Part, fraction: &mut (i128, i128)) {
        let s = Z2Part(true);
        match me {
            Z3Part::STZero => {}
            Z3Part::STOne => {
                fraction.0 += fraction.1;
                s_action(&s, fraction);
            }
            Z3Part::STTwo => {
                fraction.0 += fraction.1;
                s_action(&s, fraction);
                fraction.0 += fraction.1;
                s_action(&s, fraction);
            }
        }
    }
    impl FinitelyPresentedGroup for Z3Part {
        fn generator(_n: usize) -> Self {
            Self::STOne
        }

        fn num_generators() -> usize {
            1
        }
    }
}

mod test {

    #[test]
    fn psl2z() {
        use super::test_setup::{s_action, st_action, Z2Part, Z3Part};
        use super::{FewAssum, SimplyAmalgamatedProduct};
        use crate::fp_gp::FinitelyPresentedWords;
        use num::One;

        type PSL2Z = SimplyAmalgamatedProduct<Z2Part, Z3Part, FewAssum<Z2Part, Z3Part>>;
        let x = PSL2Z::one();
        assert!(x.my_am == FewAssum::Free);
        assert_eq!(x.pieces.len(), 0);
        let y = x.clone() * x.clone() * x.clone() * x.clone() * x.clone();
        assert_eq!(y.pieces.len(), 0);
        assert!(y.my_am == FewAssum::Free);

        let mut s = PSL2Z::one();
        s.pieces.push((Z2Part(true), Z3Part::one()));
        assert_eq!(s.pieces.len(), 1);
        assert_eq!(s.pieces[0], (Z2Part(true), Z3Part::one()));
        let y = s.clone() * s.clone();
        assert_eq!(y.pieces.len(), 0);

        let mut st = PSL2Z::one();
        st.pieces.push((Z2Part::one(), Z3Part::STOne));
        assert_eq!(st.pieces.len(), 1);
        let mut y = st.clone() * st.clone();
        assert_eq!(y.pieces.len(), 1);
        assert_eq!(y.pieces[0], (Z2Part::one(), Z3Part::STTwo));
        y *= st.clone();
        assert_eq!(y.pieces.len(), 0);

        let mut t = PSL2Z::one();
        t.pieces.push((Z2Part(true), Z3Part::STOne));
        assert!(s.clone() * st.clone() == t);
        assert_eq!(t.pieces.len(), 1);
        let mut y = t.clone() * t.clone();
        assert!(s.clone() * st.clone() * s.clone() * st.clone() == y);
        assert_eq!(y.pieces.len(), 2);
        y *= t.clone();
        assert!(s.clone() * st.clone() * s.clone() * st.clone() * s.clone() * st.clone() == y);
        assert_eq!(y.pieces.len(), 3);

        let mut psl2z_iter = FinitelyPresentedWords::<PSL2Z>::new();
        let should_iden = psl2z_iter.next();
        assert!(should_iden.is_some_and(|g| g.0.is_one()));
        let should_s = psl2z_iter.next();
        assert!(should_s.is_some_and(|g| g.0 == s));
        let should_st = psl2z_iter.next();
        assert!(should_st.is_some_and(|g| g.0 == st));
        let should_ss = psl2z_iter.next();
        assert!(should_ss.is_some_and(|g| g.0 == s.clone() * s));
        let mut farey = (1, 0);
        s_action(&Z2Part(true), &mut farey);
        assert_eq!(farey, (0, 1));
        st_action(&Z3Part::STOne, &mut farey);
        assert_eq!(farey, (-1, 1));
        st_action(&Z3Part::STOne, &mut farey);
        assert_eq!(farey, (-1, 0));
        st_action(&Z3Part::STOne, &mut farey);
        assert_eq!(farey, (0, -1));
        s_action(&Z2Part(true), &mut farey);
        assert_eq!(farey, (1, 0));
        for temp in psl2z_iter.take(10).map(|z| z.0) {
            temp.right_act(s_action, st_action, &mut farey);
        }
    }

    #[test]
    fn z6() {
        use super::test_setup::{Z2Part, Z3Part};
        use super::{FewAssum, SimplyAmalgamatedProduct};
        use num::One;

        type Z6 = SimplyAmalgamatedProduct<Z2Part, Z3Part, FewAssum<Z2Part, Z3Part>>;
        let my_ident: Z6 = Z6::from_free_version(Z6::one(), FewAssum::SomeCommuting(|_, _| true));
        assert!(match my_ident.my_am {
            FewAssum::Free => false,
            FewAssum::SomeCommuting(g) => {
                let temp1 = g(&Z2Part(true), &Z3Part::STZero)
                    && g(&Z2Part(true), &Z3Part::STOne)
                    && g(&Z2Part(true), &Z3Part::STTwo);
                let temp2 = g(&Z2Part(false), &Z3Part::STZero)
                    && g(&Z2Part(false), &Z3Part::STOne)
                    && g(&Z2Part(false), &Z3Part::STTwo);
                temp1 && temp2
            }
            FewAssum::ResourceBasedCommuting(_) => false,
        });
        assert_eq!(my_ident.pieces.len(), 0);
        let y: Z6 = my_ident.clone()
            * my_ident.clone()
            * my_ident.clone()
            * my_ident.clone()
            * my_ident.clone();
        assert_eq!(y.pieces.len(), 0);

        let mut s: Z6 = my_ident.clone();
        s.pieces.push((Z2Part(true), Z3Part::one()));
        assert_eq!(s.pieces.len(), 1);
        assert_eq!(s.pieces[0], (Z2Part(true), Z3Part::one()));
        let y: Z6 = s.clone() * s.clone();
        assert_eq!(y.pieces.len(), 0);
        assert!(match y.my_am {
            FewAssum::Free => false,
            FewAssum::SomeCommuting(g) => {
                let temp1 = g(&Z2Part(true), &Z3Part::STZero)
                    && g(&Z2Part(true), &Z3Part::STOne)
                    && g(&Z2Part(true), &Z3Part::STTwo);
                let temp2 = g(&Z2Part(false), &Z3Part::STZero)
                    && g(&Z2Part(false), &Z3Part::STOne)
                    && g(&Z2Part(false), &Z3Part::STTwo);
                temp1 && temp2
            }
            FewAssum::ResourceBasedCommuting(_) => false,
        });

        let mut st: Z6 = my_ident.clone();
        st.pieces.push((Z2Part::one(), Z3Part::STOne));
        assert_eq!(st.pieces.len(), 1);
        let mut y: Z6 = st.clone() * st.clone();
        assert_eq!(y.pieces.len(), 1);
        assert_eq!(y.pieces[0], (Z2Part::one(), Z3Part::STTwo));
        y *= st.clone();
        assert_eq!(y.pieces.len(), 0);

        let mut t: Z6 = my_ident.clone();
        t.pieces.push((Z2Part(true), Z3Part::STOne));
        assert!(s.clone() * st.clone() == t);
        assert_eq!(t.pieces.len(), 1);
        let mut y: Z6 = t.clone() * t.clone();
        assert!(s.clone() * st.clone() * s.clone() * st.clone() == y);
        assert_eq!(y.pieces.len(), 1);
        assert_eq!(y.pieces[0], (Z2Part(false), Z3Part::STTwo));
        for idx in 3..6 {
            y *= t.clone();
            assert_eq!(y.pieces.len(), 1);
            let cur_z2_part = Z2Part(if idx % 2 == 0 { false } else { true });
            let idx_mod_3 = idx % 3;
            let cur_z3_part = if idx_mod_3 == 0 {
                Z3Part::STZero
            } else if idx_mod_3 == 1 {
                Z3Part::STOne
            } else {
                Z3Part::STTwo
            };
            assert_eq!(y.pieces[0], (cur_z2_part, cur_z3_part));
        }
        y *= t.clone();
        assert_eq!(y.pieces.len(), 0);
    }
}
