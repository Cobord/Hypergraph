use itertools::Itertools;
use std::cmp::{max, min};
use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;
use std::mem::swap;
use std::ops::{Add, AddAssign, Mul, MulAssign};

use num::{One, Zero};
use petgraph::algo::{connected_components, has_path_connecting, DfsSpace};
use petgraph::{Graph, Undirected};

use crate::category::{Composable, HasIdentity};
use crate::finset::is_monotonic_inc;
use crate::linear_combination::{
    inj_linearly_extend, linear_combine, linearly_extend, simplify as linear_simplify,
    LinearCombination,
};
use crate::monoidal::{Monoidal, MonoidalMorphism};

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
struct PerfectMatching {
    pairs: Vec<(usize, usize)>,
}

impl PerfectMatching {
    fn new(pair_prime: &[(usize, usize)]) -> Self {
        let max_expected = pair_prime.len() * 2;
        let mut cur_seen = HashSet::with_capacity(max_expected);
        for (p, q) in pair_prime {
            assert!(*p < max_expected);
            assert!(*q < max_expected);
            cur_seen.insert(*p);
            cur_seen.insert(*q);
        }
        assert_eq!(cur_seen.len(), max_expected);
        let pair_iter = pair_prime.iter().copied();
        let mut ret_val = Self {
            pairs: Vec::from_iter(pair_iter),
        };
        ret_val.canonicalize();
        ret_val
    }

    fn canonicalize(&mut self) {
        for (p, q) in self.pairs.iter_mut() {
            if *p > *q {
                swap(p, q);
            }
        }
        self.pairs.sort();
    }

    fn flip_upside_down(&self, source: usize, target: usize) -> Self {
        let new_list = self.pairs.iter().map(|(z, w)| {
            let new_z = if *z < source { z + target } else { z - source };
            let new_w = if *w < source { w + target } else { w - source };
            (new_z, new_w)
        });
        Self::new(&new_list.collect::<Vec<(usize, usize)>>())
    }

    fn non_crossing(&self, source: usize, _target: usize) -> bool {
        // todo simplify
        let in_between = |query, (interval1, interval2)| {
            (query < interval1 && query > interval2) || (query < interval2 && query > interval1)
        };
        let source_lines = self
            .pairs
            .iter()
            .filter(|(z, w)| *z < source && *w < source)
            .cloned();
        let source_crossing_tests = source_lines.clone().combinations(2);
        for cur_item in source_crossing_tests {
            let first_block = cur_item[0];
            let second_block = cur_item[1];
            let a = in_between(second_block.0, first_block);
            let b = in_between(second_block.1, first_block);
            if a != b {
                return false;
            }
        }
        let mut no_through_lines_idx = HashSet::<usize>::new();
        for (x, y) in source_lines {
            for z in (1 + min(x, y))..max(x, y) {
                no_through_lines_idx.insert(z);
            }
        }
        let target_lines = self
            .pairs
            .iter()
            .filter(|(z, w)| *z >= source && *w >= source)
            .cloned();
        let target_crossing_tests = target_lines.clone().combinations(2);
        for cur_item in target_crossing_tests {
            let first_block = cur_item[0];
            let second_block = cur_item[1];
            let a = in_between(second_block.0, first_block);
            let b = in_between(second_block.1, first_block);
            if a != b {
                return false;
            }
        }
        for (x, y) in target_lines {
            for z in (1 + min(x, y))..max(x, y) {
                no_through_lines_idx.insert(z);
            }
        }
        let through_lines = self
            .pairs
            .iter()
            .filter(|(z, w)| (*z < source && *w >= source) || (*w < source && *z >= source))
            .map(|(z, w)| (min(*z, *w), max(*z, *w)));
        for cur in through_lines.clone() {
            if no_through_lines_idx.contains(&cur.0) || no_through_lines_idx.contains(&cur.1) {
                return false;
            }
        }
        is_monotonic_inc(through_lines.map(|(_, w)| w), None)
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
struct ExtendedPerfectMatching((usize, usize, usize, PerfectMatching));

impl Mul for ExtendedPerfectMatching {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let (self_dom, self_cod, self_delta_pow, self_diagram) = self.0;
        let (rhs_dom, rhs_cod, rhs_delta_pow, rhs_diagram) = rhs.0;
        assert_eq!(rhs_dom, self_cod);
        let mut g: Graph<(), (), Undirected> = Graph::new_undirected();
        let mut node_idcs = Vec::with_capacity(self_dom + self_cod + rhs_cod);
        for _ in 0..self_dom + self_cod + rhs_cod {
            node_idcs.push(None);
        }
        let self_pairs_copy = self_diagram.pairs.clone();
        for (p, q) in self_diagram.pairs {
            let p_loc = g.add_node(());
            node_idcs[p] = Some(p_loc);
            let q_loc = g.add_node(());
            node_idcs[q] = Some(q_loc);
            g.add_edge(p_loc, q_loc, ());
        }
        for (idx, cur_item) in node_idcs.iter().enumerate().take(self_dom + self_cod) {
            if cur_item.is_none() {
                panic!(
                    "index for {idx} unset. These were the ones in self_diagram {:?}",
                    self_pairs_copy
                );
            }
        }
        let rhs_pairs_copy = rhs_diagram.pairs.clone();
        for (p, q) in rhs_diagram.pairs {
            let p_loc = if p >= rhs_dom {
                let p_loc_temp = g.add_node(());
                node_idcs[p + self_dom] = Some(p_loc_temp);
                p_loc_temp
            } else {
                node_idcs[p + self_dom].unwrap()
            };
            let q_loc = if q >= rhs_dom {
                let q_loc_temp = g.add_node(());
                node_idcs[q + self_dom] = Some(q_loc_temp);
                q_loc_temp
            } else {
                node_idcs[q + self_dom].unwrap()
            };
            g.add_edge(p_loc, q_loc, ());
        }
        for (idx, cur_item) in node_idcs.iter().enumerate() {
            if cur_item.is_none() {
                panic!(
                    "index for {idx} unset. These were the ones in rhs {:?}",
                    rhs_pairs_copy
                );
            }
        }
        let endpoints = self_dom + rhs_cod;
        let mut endpoints_done: HashSet<usize> = HashSet::with_capacity(endpoints);
        let mut workspace = DfsSpace::new(&g);
        let mut final_matching = Vec::with_capacity(endpoints / 2);
        for i in 0..endpoints {
            if endpoints_done.contains(&i) {
                continue;
            }
            let i_loc = (if i < self_dom {
                node_idcs[i]
            } else {
                node_idcs[i + self_cod]
            })
            .unwrap();
            for j in (i + 1)..endpoints {
                let j_loc = (if j < self_dom {
                    node_idcs[j]
                } else {
                    node_idcs[j + self_cod]
                })
                .unwrap();
                let ij_conn = has_path_connecting(&g, i_loc, j_loc, Some(&mut workspace));
                if ij_conn {
                    final_matching.push((i, j));
                    endpoints_done.insert(i);
                    endpoints_done.insert(j);
                    break;
                }
            }
        }
        let new_delta_power =
            connected_components(&g) + self_delta_pow + rhs_delta_pow - (endpoints / 2);
        Self((
            self_dom,
            rhs_cod,
            new_delta_power,
            PerfectMatching::new(&final_matching),
        ))
    }
}

pub struct BrauerMorphism<T>
where
    T: Add<Output = T> + Zero + One + Copy,
{
    my_diagram: LinearCombination<T, (usize, PerfectMatching)>,
    source: usize,
    target: usize,
    is_def_tl: bool,
}

impl<T> PartialEq for BrauerMorphism<T>
where
    T: Add<Output = T> + Zero + One + Copy + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        self.my_diagram == other.my_diagram
            && self.source == other.source
            && self.target == other.target
    }
}

impl<T> Clone for BrauerMorphism<T>
where
    T: Add<Output = T> + Zero + One + Copy,
{
    fn clone(&self) -> Self {
        Self {
            my_diagram: self.my_diagram.clone(),
            source: self.source,
            target: self.target,
            is_def_tl: self.is_def_tl,
        }
    }
}

impl<T> Debug for BrauerMorphism<T>
where
    T: Add<Output = T> + Zero + One + Copy + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BrauerMorphism")
            .field("my_diagram", &self.my_diagram)
            .field("source", &self.source)
            .field("target", &self.target)
            .field("is_def_tl", &self.is_def_tl)
            .finish()
    }
}

impl<T> HasIdentity<usize> for BrauerMorphism<T>
where
    T: Add<Output = T> + Zero + One + Copy,
{
    fn identity(on_this: &usize) -> Self {
        let my_matching = (0..*on_this)
            .map(|x| (x, x + on_this))
            .collect::<Vec<(usize, usize)>>();
        let my_perfect_matching = PerfectMatching::new(&my_matching);
        Self {
            my_diagram: LinearCombination::<T, (usize, PerfectMatching)>::singleton((
                0,
                my_perfect_matching,
            )),
            source: *on_this,
            target: *on_this,
            is_def_tl: true,
        }
    }
}

impl<T> Composable<usize> for BrauerMorphism<T>
where
    T: Add<Output = T> + Zero + One + Copy + AddAssign + Mul<Output = T> + MulAssign,
{
    fn compose(&self, other: &Self) -> Result<Self, String> {
        self.composable(other)?;
        let extended_diagram_self =
            inj_linearly_extend(&self.my_diagram, |(delta_pow, diagram)| {
                ExtendedPerfectMatching((self.domain(), self.codomain(), delta_pow, diagram))
            });
        let extended_diagram_other =
            inj_linearly_extend(&other.my_diagram, |(delta_pow, diagram)| {
                ExtendedPerfectMatching((other.domain(), other.codomain(), delta_pow, diagram))
            });
        let extended_diagram_product = extended_diagram_self * extended_diagram_other;
        let diagram_product = linearly_extend(&extended_diagram_product, |extended| {
            (extended.0 .2, extended.0 .3)
        });
        Ok(Self {
            my_diagram: diagram_product,
            source: self.domain(),
            target: other.codomain(),
            is_def_tl: self.is_def_tl && other.is_def_tl,
        })
    }

    fn domain(&self) -> usize {
        self.source
    }

    fn codomain(&self) -> usize {
        self.target
    }
}

impl<T> Monoidal for BrauerMorphism<T>
where
    T: Add<Output = T> + Zero + One + Copy + AddAssign + Mul<Output = T> + MulAssign,
{
    fn monoidal(&mut self, other: Self) {
        let old_domain = self.domain();
        let old_codomain = self.codomain();
        let other_domain = other.domain();
        self.source += other_domain;
        self.target += other.codomain();
        let new_domain = self.domain();
        self.is_def_tl &= other.is_def_tl;
        let shift_idx = |diagram: PerfectMatching, if_above, shift_amount| {
            PerfectMatching::new(
                &diagram
                    .pairs
                    .iter()
                    .map(|(x, y)| {
                        let new_x = if *x >= if_above {
                            *x + shift_amount
                        } else {
                            *x
                        };
                        let new_y = if *y >= if_above {
                            *y + shift_amount
                        } else {
                            *y
                        };
                        (new_x, new_y)
                    })
                    .collect::<Vec<(usize, usize)>>(),
            )
        };
        self.my_diagram = linear_combine(
            self.my_diagram.clone(),
            other.my_diagram,
            |(delta_pow1, matching_1), (delta_pow2, matching2)| {
                let mut new_matching = shift_idx(matching_1, old_domain, other_domain);
                let mut other_shifted = shift_idx(matching2, 0, old_domain);
                other_shifted = shift_idx(other_shifted, new_domain, old_codomain);
                new_matching.pairs.extend(other_shifted.pairs);
                new_matching.canonicalize();
                (delta_pow1 + delta_pow2, new_matching)
            },
        );
    }
}

impl<T> MonoidalMorphism<usize> for BrauerMorphism<T> where
    T: Add<Output = T> + Zero + One + Copy + AddAssign + Mul<Output = T> + MulAssign
{
}

impl<T> BrauerMorphism<T>
where
    T: Add<Output = T> + Zero + One + Copy + AddAssign + Mul<Output = T> + MulAssign,
{
    #[allow(dead_code)]
    pub fn temperley_lieb_gens(n: usize) -> Vec<Self> {
        let mut ret_val = Vec::with_capacity(n - 1);
        for i in 0..(n - 1) {
            let mut e_i_pairs = Vec::with_capacity(2 * n);
            for j in 0..n {
                if j == i {
                    e_i_pairs.push((i, i + 1));
                } else if j == i + 1 {
                    e_i_pairs.push((i + n, i + 1 + n));
                } else {
                    e_i_pairs.push((j, j + n));
                }
            }
            let e_i_matching = PerfectMatching::new(&e_i_pairs);
            let cur_e_i = Self {
                my_diagram: LinearCombination::<T, (usize, PerfectMatching)>::singleton((
                    0,
                    e_i_matching,
                )),
                source: n,
                target: n,
                is_def_tl: true,
            };
            ret_val.push(cur_e_i);
        }
        ret_val
    }

    #[allow(dead_code)]
    pub fn symmetric_alg_gens(n: usize) -> Vec<Self> {
        let mut ret_val = Vec::with_capacity(n);
        for i in 0..(n - 1) {
            let mut e_i_pairs = Vec::with_capacity(2 * n);
            for j in 0..n {
                if j == i {
                    e_i_pairs.push((i, i + n + 1));
                } else if j == i + 1 {
                    e_i_pairs.push((i + 1, i + n));
                } else {
                    e_i_pairs.push((j, j + n));
                }
            }
            let e_i_matching = PerfectMatching::new(&e_i_pairs);
            let cur_e_i = Self {
                my_diagram: LinearCombination::<T, (usize, PerfectMatching)>::singleton((
                    0,
                    e_i_matching,
                )),
                source: n,
                target: n,
                is_def_tl: false,
            };
            ret_val.push(cur_e_i);
        }
        ret_val
    }

    pub fn delta_polynomial(coeffs: &[T]) -> Self {
        let zeroth_coeff = if coeffs.is_empty() {
            T::zero()
        } else {
            coeffs[0]
        };
        let empty_matching = PerfectMatching { pairs: vec![] };
        let mut my_diagram =
            LinearCombination::<T, (usize, PerfectMatching)>::singleton((0, empty_matching));
        my_diagram *= zeroth_coeff;
        for (idx, cur_coeff) in coeffs.iter().enumerate().skip(1) {
            let empty_matching = PerfectMatching { pairs: vec![] };
            let mut cur_diagram =
                LinearCombination::<T, (usize, PerfectMatching)>::singleton((idx, empty_matching));
            cur_diagram *= *cur_coeff;
            my_diagram += cur_diagram;
        }
        Self {
            my_diagram,
            source: 0,
            target: 0,
            is_def_tl: true,
        }
    }

    #[allow(dead_code)]
    pub fn dagger<F>(&self, num_dagger: F) -> Self
    where
        F: Fn(T) -> T,
    {
        let flip_upside_down = |(delta_pow, matching): (usize, PerfectMatching)| {
            (
                delta_pow,
                matching.flip_upside_down(self.source, self.target),
            )
        };
        let mut my_diagram = inj_linearly_extend(&self.my_diagram, flip_upside_down);
        my_diagram.change_coeffs(num_dagger);
        Self {
            my_diagram,
            source: self.target,
            target: self.source,
            is_def_tl: self.is_def_tl,
        }
    }

    #[allow(dead_code)]
    pub fn set_is_tl(&mut self) {
        if self.is_def_tl {
            return;
        }
        let is_non_crossing =
            |(_, p): &(usize, PerfectMatching)| p.non_crossing(self.source, self.target);
        self.is_def_tl = self.my_diagram.all_terms_satisfy(is_non_crossing);
    }
}

fn simplify<T>(me: &mut BrauerMorphism<T>)
where
    T: Add<Output = T> + Zero + One + Copy + AddAssign + Mul<Output = T> + MulAssign + Eq,
{
    linear_simplify(&mut me.my_diagram);
}

mod test {
    use std::fmt::Debug;
    use std::ops::{AddAssign, MulAssign};

    use super::BrauerMorphism;
    use either::Either;
    use num::{One, Zero};

    #[allow(dead_code)]
    fn test_helper<T: Eq + AddAssign + MulAssign + Copy + One + Zero>(
        e_i: &[BrauerMorphism<T>],
        s_i: &[BrauerMorphism<T>],
        prod_these: &[Either<usize, usize>],
        delta_poly_coeffs: &[T],
    ) -> Result<BrauerMorphism<T>, String> {
        fn get_generator<T: Clone>(l_gens: &[T], r_gens: &[T], which: Either<usize, usize>) -> T {
            use crate::utils::either_f;
            either_f(which, |n| l_gens[n].clone(), |n| r_gens[n].clone())
        }
        use super::simplify;
        use crate::category::Composable;
        use crate::monoidal::Monoidal;
        assert!(!prod_these.is_empty());
        let prod_these_0 = get_generator(e_i, s_i, prod_these[0]);
        let mut delta_poly = BrauerMorphism::delta_polynomial(delta_poly_coeffs);
        simplify(&mut delta_poly);
        if prod_these.len() == 1 {
            let mut full_prod = prod_these_0;
            full_prod.monoidal(delta_poly);
            return Ok(full_prod);
        }
        let prod_these_1 = get_generator(e_i, s_i, prod_these[1]);
        let mut full_prod = prod_these_0.compose(&prod_these_1);
        for cur_idx in prod_these.iter().skip(2) {
            let cur = get_generator(e_i, s_i, *cur_idx);
            full_prod = full_prod.and_then(|z| z.compose(&cur));
        }
        match full_prod {
            Ok(mut t) => {
                t.monoidal(delta_poly);
                Ok(t)
            }
            Err(e) => Err(e),
        }
    }

    #[allow(dead_code)]
    fn test_asserter<T, U, F>(
        observed: Result<T, U>,
        expected: Result<T, U>,
        aux_test: F,
        equation_str: &str,
    ) where
        F: Fn(&T, &T) -> bool,
        T: Debug + PartialEq,
    {
        match (observed, expected) {
            (Ok(real_observed), Ok(real_expected)) => {
                assert!(aux_test(&real_observed, &real_expected));
                assert!(
                    PartialEq::eq(&real_observed, &real_expected),
                    "{:?} vs {:?} when checking {:?}",
                    real_observed,
                    real_expected,
                    equation_str
                );
            }
            _ => panic!(
                "Error on one of observed/expected sides when checking {:?}",
                equation_str
            ),
        }
    }

    #[test]
    fn t_l_relations() {
        use crate::category::Composable;
        use either::Either::Left;
        use num::Complex;
        use std::cmp::PartialEq;
        let e_i = BrauerMorphism::<Complex<i32>>::temperley_lieb_gens(5);
        let zero_complex = Complex::<i32>::zero();
        let one_complex = Complex::<i32>::one();
        let delta_coeffs = [zero_complex, one_complex];
        for idx in 0..e_i.len() {
            assert!(e_i[idx].is_def_tl);
            let e_i_dag = e_i[idx].dagger(|z| z.conj());
            assert!(
                PartialEq::eq(&e_i[idx], &e_i_dag),
                "{:?} vs {:?} when checking self adjointness of e_i",
                e_i[idx],
                e_i_dag
            );
            let e_ie_i = e_i[idx].compose(&e_i[idx]);
            let deltae_i = test_helper(&e_i, &[], &[Left(idx)], &delta_coeffs);
            test_asserter(
                e_ie_i,
                deltae_i,
                |j, k| j.is_def_tl && k.is_def_tl,
                "e_i e_i = delta e_i",
            );
            if idx < e_i.len() - 1 {
                let prod_iji = e_i[idx]
                    .compose(&e_i[idx + 1])
                    .and_then(|z| z.compose(&e_i[idx]));
                test_asserter(
                    prod_iji,
                    Ok(e_i[idx].clone()),
                    |j, k| j.is_def_tl && k.is_def_tl,
                    "e_i e_(i+1) e_i = e_i",
                );
            }
            if idx > 1 {
                let prod_iji = e_i[idx]
                    .compose(&e_i[idx - 1])
                    .and_then(|z| z.compose(&e_i[idx]));
                test_asserter(
                    prod_iji,
                    Ok(e_i[idx].clone()),
                    |j, k| j.is_def_tl && k.is_def_tl,
                    "e_i e_(i-1) e_i = e_i",
                );
            }
            for jdx in idx + 2..e_i.len() {
                let prod_ij = e_i[idx].compose(&e_i[jdx]);
                let prod_ji = e_i[jdx].compose(&e_i[idx]);
                test_asserter(
                    prod_ij,
                    prod_ji,
                    |j, k| j.is_def_tl && k.is_def_tl,
                    "e_i e_j = e_j e_i",
                );
            }
        }
    }

    #[test]
    fn wiki_example() {
        use super::{simplify, BrauerMorphism};
        use crate::category::Composable;
        use crate::monoidal::Monoidal;
        use num::Complex;
        use num::{One, Zero};
        let e_i = BrauerMorphism::<Complex<i32>>::temperley_lieb_gens(5);
        let zero_complex = Complex::<i32>::zero();
        let one_complex = Complex::<i32>::one();
        let prod_1432 = e_i[0]
            .compose(&e_i[3])
            .and_then(|z| z.compose(&e_i[2]))
            .and_then(|z| z.compose(&e_i[1]));
        let prod_243 = e_i[1].compose(&e_i[3]).and_then(|z| z.compose(&e_i[2]));
        let prod_143243 = e_i[0]
            .compose(&e_i[3])
            .and_then(|z| z.compose(&e_i[2]))
            .and_then(|z| z.compose(&e_i[1]))
            .and_then(|z| z.compose(&e_i[3]))
            .and_then(|z| z.compose(&e_i[2]));
        let observed = prod_1432.and_then(|z| match prod_243 {
            Ok(real_prod_243) => z.compose(&real_prod_243),
            Err(e) => Err(e),
        });
        let mut expected =
            BrauerMorphism::<Complex<i32>>::delta_polynomial(&[zero_complex, one_complex]);
        simplify(&mut expected);
        match (observed, prod_143243) {
            (Ok(real_obs), Ok(exp_wo_delta)) => {
                assert!(real_obs.is_def_tl);
                expected.monoidal(exp_wo_delta);
                assert!(expected.is_def_tl);
                assert!(PartialEq::eq(&real_obs, &expected));
            }
            _ => {
                panic!("Error in composition when checking (e_1 e_4 e_3 e_2) (e_2 e_4 e_3) = delta e_1 e_4 e_3 e_2 e_4 e_3")
            }
        }
    }

    #[test]
    fn sym_relations() {
        use super::BrauerMorphism;
        use crate::category::{Composable, HasIdentity};
        use either::Either::Right;
        use num::Complex;
        let n = 7;
        let s_i = BrauerMorphism::<Complex<i32>>::symmetric_alg_gens(n);
        let one_poly_coeffs = [Complex::<i32>::one()];
        let my_identity = BrauerMorphism::<Complex<i32>>::identity(&n);
        for idx in 0..n - 1 {
            assert!(!s_i[idx].is_def_tl);
            let s_i_dag = s_i[idx].dagger(|z| z.conj());
            assert!(
                PartialEq::eq(&s_i[idx], &s_i_dag),
                "{:?} vs {:?} when checking self adjointness of s_i",
                s_i[idx],
                s_i_dag
            );
            let s_is_i = s_i[idx].compose(&s_i[idx]);
            test_asserter(
                s_is_i,
                Ok(my_identity.clone()),
                |j, k| !j.is_def_tl && k.is_def_tl,
                "s_i s_i = 1",
            );
            if idx < n - 2 {
                let s_is_js_i = test_helper(
                    &[],
                    &s_i,
                    &[Right(idx), Right(idx + 1), Right(idx)],
                    &one_poly_coeffs,
                );
                let s_js_is_j = test_helper(
                    &[],
                    &s_i,
                    &[Right(idx + 1), Right(idx), Right(idx + 1)],
                    &one_poly_coeffs,
                );
                test_asserter(
                    s_is_js_i,
                    s_js_is_j,
                    |j, k| !j.is_def_tl && !k.is_def_tl,
                    "s_i s_(i+1) s_i = s_(i+1) s_i s_(i+1)",
                );
            }
            if idx > 1 {
                let s_is_js_i = test_helper(
                    &[],
                    &s_i,
                    &[Right(idx), Right(idx - 1), Right(idx)],
                    &one_poly_coeffs,
                );
                let s_js_is_j = test_helper(
                    &[],
                    &s_i,
                    &[Right(idx - 1), Right(idx), Right(idx - 1)],
                    &one_poly_coeffs,
                );
                test_asserter(
                    s_is_js_i,
                    s_js_is_j,
                    |j, k| !j.is_def_tl && !k.is_def_tl,
                    "s_i s_(i-1) s_i = s_(i-1) s_i s_(i-1)",
                );
            }
            for jdx in idx + 2..s_i.len() {
                let prod_ij = s_i[idx].compose(&s_i[jdx]);
                let prod_ji = s_i[jdx].compose(&s_i[idx]);
                test_asserter(
                    prod_ij,
                    prod_ji,
                    |j, k| !j.is_def_tl && !k.is_def_tl,
                    "s_i s_j = s_j s_i",
                );
            }
        }
    }

    #[test]
    fn tangle_relations() {
        use super::BrauerMorphism;
        use crate::category::Composable;
        use either::Either::{Left, Right};
        use num::Complex;
        let n = 7;
        let s_i = BrauerMorphism::<Complex<i32>>::symmetric_alg_gens(n);
        let e_i = BrauerMorphism::<Complex<i32>>::temperley_lieb_gens(n);
        let one_poly_coeffs = [Complex::<i32>::one()];
        for idx in 0..n - 1 {
            let e_is_i = e_i[idx].compose(&s_i[idx]);
            let s_ie_i: Result<BrauerMorphism<Complex<i32>>, String> = s_i[idx].compose(&e_i[idx]);
            test_asserter(
                e_is_i,
                Ok(e_i[idx].clone()),
                |j, k| !j.is_def_tl && k.is_def_tl,
                "e_i s_i = e_i",
            );
            test_asserter(
                s_ie_i,
                Ok(e_i[idx].clone()),
                |j, k| !j.is_def_tl && k.is_def_tl,
                "s_i e_i = e_i",
            );
            if idx < n - 2 {
                let s_is_je_i = test_helper(
                    &e_i,
                    &s_i,
                    &[Right(idx), Right(idx + 1), Left(idx)],
                    &one_poly_coeffs,
                );
                let e_je_i = test_helper(&e_i, &s_i, &[Left(idx + 1), Left(idx)], &one_poly_coeffs);
                test_asserter(
                    s_is_je_i,
                    e_je_i,
                    |j, k| !j.is_def_tl && k.is_def_tl,
                    "s_i s_(i+1) e_i = e_(i+1) e_i",
                );
                let e_is_je_i = test_helper(
                    &e_i,
                    &s_i,
                    &[Left(idx), Right(idx + 1), Left(idx)],
                    &one_poly_coeffs,
                );
                test_asserter(
                    e_is_je_i,
                    Ok(e_i[idx].clone()),
                    |j, k| !j.is_def_tl && k.is_def_tl,
                    "e_i s_(i+1) e_i = e_i",
                );
            }
            if idx > 1 {
                let s_is_je_i = test_helper(
                    &e_i,
                    &s_i,
                    &[Right(idx), Right(idx - 1), Left(idx)],
                    &one_poly_coeffs,
                );
                let e_je_i = test_helper(&e_i, &s_i, &[Left(idx - 1), Left(idx)], &one_poly_coeffs);
                test_asserter(
                    s_is_je_i,
                    e_je_i,
                    |j, k| !j.is_def_tl && k.is_def_tl,
                    "s_i s_(i-1) e_i = e_(i-1) e_i",
                );
                let e_is_je_i = test_helper(
                    &e_i,
                    &s_i,
                    &[Left(idx), Right(idx - 1), Left(idx)],
                    &one_poly_coeffs,
                );
                test_asserter(
                    e_is_je_i,
                    Ok(e_i[idx].clone()),
                    |j, k| !j.is_def_tl && k.is_def_tl,
                    "e_i s_(i-1) e_i = e_i",
                );
            }
            for jdx in idx + 2..s_i.len() {
                let prod_ij = s_i[idx].compose(&e_i[jdx]);
                let prod_ji = e_i[jdx].compose(&s_i[idx]);
                test_asserter(
                    prod_ij,
                    prod_ji,
                    |j, k| !j.is_def_tl && !k.is_def_tl,
                    "s_i e_j = e_j s_i",
                );
            }
        }
    }
}
