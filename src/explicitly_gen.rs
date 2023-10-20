use itertools::Itertools;
use std::{
    iter::zip,
    ops::{DivAssign, Mul, MulAssign},
    rc::Rc,
};

type GeneratorOrder = Option<usize>;
type GeneratorLabel = usize;
type GeneratorPower = usize;

#[derive(PartialEq, Eq, Clone)]
#[allow(dead_code)]
pub struct ExplicitlyGenerated<T: Mul<Output = T> + Clone + Eq> {
    underlying: T,
    as_word: Vec<(GeneratorLabel, GeneratorPower)>,
    gens: Rc<Vec<(T, GeneratorOrder)>>,
    commuting_gens: Rc<Vec<(GeneratorLabel, GeneratorLabel)>>,
    ident_t: T,
}

impl<T> ExplicitlyGenerated<T>
where
    T: Mul<Output = T> + Clone + Eq,
{
    #[allow(dead_code)]
    pub fn new(generators: Vec<T>, orders: Vec<GeneratorOrder>, identity: T) -> Self {
        let mut pairs_commute = Vec::with_capacity(generators.len());
        for pair in (0..generators.len()).combinations(2) {
            let p0 = pair[0];
            let p1 = pair[1];
            let g0g1 = generators[p0].clone() * generators[p1].clone();
            let g1g0 = generators[p1].clone() * generators[p0].clone();
            if g0g1 == g1g0 {
                pairs_commute.push((p0, p1));
            }
        }
        Self {
            underlying: identity.clone(),
            as_word: vec![],
            gens: Rc::new(zip(generators, orders).collect_vec()),
            commuting_gens: Rc::new(pairs_commute),
            ident_t: identity,
        }
    }

    #[allow(dead_code)]
    pub fn generator(&self, n: GeneratorLabel) -> Self {
        let real_n = n % self.num_generators();
        Self {
            underlying: self.gens[real_n].0.clone(),
            as_word: vec![(real_n, 1)],
            gens: self.gens.clone(),
            commuting_gens: self.commuting_gens.clone(),
            ident_t: self.ident_t.clone(),
        }
    }

    pub fn num_generators(&self) -> GeneratorLabel {
        self.gens.len()
    }

    pub fn all_gens_orders(&self) -> Vec<GeneratorOrder> {
        self.gens.iter().map(|z| z.1).collect_vec()
    }

    #[allow(dead_code)]
    fn condense_word_full(&mut self, where_to_look: Option<Vec<usize>>, max_passes: i8) {
        let mut next_batch = self.condense_word(where_to_look);
        let mut pass_number = 1;
        while !next_batch.is_empty() {
            next_batch = self.condense_word(Some(next_batch));
            pass_number += 1;
            if pass_number >= max_passes {
                break;
            }
        }
    }

    fn condense_word(&mut self, where_to_look: Option<Vec<usize>>) -> Vec<usize> {
        if let Some(mut real_where_to_look) = where_to_look {
            let gen_orders = self.all_gens_orders().clone();
            real_where_to_look.sort();
            real_where_to_look.dedup();
            let mut pop_count = 0;
            let max_pop_count = 2 * self.as_word.len();
            let mut leftover_concerns = Vec::with_capacity(real_where_to_look.len());
            while let Some(cur_look) = real_where_to_look.pop() {
                pop_count += 1;
                if cur_look >= self.as_word.len() {
                    continue;
                }
                let x = self.as_word[cur_look];
                if x.1 == 0 {
                    self.as_word.remove(cur_look);
                    if cur_look > 0 && pop_count < max_pop_count {
                        real_where_to_look.push(cur_look - 1);
                    } else if cur_look > 0 {
                        leftover_concerns.push(cur_look - 1);
                    }
                    continue;
                }
                if cur_look + 1 >= self.as_word.len() {
                    continue;
                }
                let y = self.as_word[cur_look + 1];
                if y.1 == 0 {
                    self.as_word.remove(cur_look + 1);
                    if pop_count < max_pop_count {
                        real_where_to_look.push(cur_look);
                    } else {
                        leftover_concerns.push(cur_look);
                    }
                    continue;
                }
                if x.0 == y.0 {
                    self.as_word[cur_look].1 += y.1;
                    if let Some(cur_order) = gen_orders[x.0] {
                        self.as_word[cur_look].1 %= cur_order;
                    }
                    self.as_word.remove(cur_look + 1);
                    if pop_count < max_pop_count {
                        real_where_to_look.push(cur_look);
                    } else {
                        leftover_concerns.push(cur_look);
                    }
                } else if x.0 > y.0
                    && (self.commuting_gens.contains(&(y.0, x.0))
                        || self.commuting_gens.contains(&(x.0, y.0)))
                {
                    self.as_word.swap(cur_look, cur_look + 1);
                    if cur_look > 0 && pop_count < max_pop_count {
                        real_where_to_look.push(cur_look - 1);
                    } else if cur_look > 0 {
                        leftover_concerns.push(cur_look - 1);
                    }
                    if pop_count < max_pop_count {
                        real_where_to_look.push(cur_look + 1);
                    } else {
                        leftover_concerns.push(cur_look + 1);
                    }
                }
            }
            let word_len = self.as_word.len();
            leftover_concerns
                .into_iter()
                .filter(|p| *p < word_len)
                .collect_vec()
        } else {
            let real_where_to_look = (0..self.as_word.len() - 1).collect_vec();
            self.condense_word(Some(real_where_to_look))
        }
    }
}

impl<T> MulAssign for ExplicitlyGenerated<T>
where
    T: Mul<Output = T> + MulAssign + Clone + Eq,
{
    fn mul_assign(&mut self, rhs: Self) {
        assert!(self.gens == rhs.gens);
        assert!(self.commuting_gens == rhs.commuting_gens);
        assert!(self.ident_t == rhs.ident_t);
        self.underlying *= rhs.underlying;
        let where_to_look = self.as_word.len();
        self.as_word.extend(rhs.as_word);
        self.condense_word(Some(vec![where_to_look - 1]));
    }
}

impl<T> DivAssign for ExplicitlyGenerated<T>
where
    T: Mul<Output = T> + DivAssign + Clone + Eq,
{
    fn div_assign(&mut self, rhs: Self) {
        assert!(self.gens == rhs.gens);
        assert!(self.commuting_gens == rhs.commuting_gens);
        assert!(self.ident_t == rhs.ident_t);
        assert!(self.all_gens_orders().iter().all(|z| z.is_some()));
        let gen_orders = rhs.all_gens_orders().clone();
        self.underlying /= rhs.underlying;
        let mut rhs_inv_word = rhs.as_word.clone();
        rhs_inv_word.reverse();
        rhs_inv_word.iter_mut().for_each(|a| {
            a.1 = gen_orders[a.0].unwrap() - a.1;
        });
        let where_to_look = self.as_word.len();
        self.as_word.extend(rhs_inv_word);
        self.condense_word(Some(vec![where_to_look - 1]));
    }
}

impl<T> Mul for ExplicitlyGenerated<T>
where
    T: Mul<Output = T> + Clone + Eq,
{
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        assert!(self.gens == rhs.gens);
        assert!(self.commuting_gens == rhs.commuting_gens);
        assert!(self.ident_t == rhs.ident_t);
        let gen_orders = rhs.all_gens_orders().clone();
        let underlying = self.underlying * rhs.underlying;
        let mut as_word = self.as_word.clone();
        let mut rhs_word = rhs.as_word;
        let as_word_last = as_word.last().copied();
        let rhs_word_first = rhs_word.first().copied();
        match (as_word_last, rhs_word_first) {
            (Some(x), Some(y)) if x.0 == y.0 => {
                as_word.pop();
                rhs_word[0].1 += x.1;
                if let Some(x0_order) = gen_orders[x.0] {
                    rhs_word[0].1 %= x0_order;
                }
            }
            _ => {}
        }
        as_word.extend(rhs_word);
        Self {
            underlying,
            as_word,
            gens: self.gens,
            commuting_gens: self.commuting_gens,
            ident_t: self.ident_t,
        }
    }
}

impl<T> Iterator for ExplicitlyGenerated<T>
where
    T: MulAssign + Mul<Output = T> + DivAssign + Clone + Eq,
{
    type Item = (T, Vec<(GeneratorLabel, GeneratorPower)>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.gens.is_empty() {
            return None;
        }
        if self.as_word.is_empty() {
            self.as_word.push((0, 1));
            self.underlying *= self.gens[0].0.clone();
            return Some((self.underlying.clone(), self.as_word.clone()));
        }
        let word_len = self.as_word.len();
        let last_step: (GeneratorLabel, GeneratorPower) = self.as_word[word_len - 1];
        if let Some(last_step_order) = self.gens[0].1 {
            if last_step.0 < last_step_order - 1 {
                self.as_word[word_len - 1].1 += 1;
                self.underlying *= self.gens[last_step.0].0.clone();
                Some((self.underlying.clone(), self.as_word.clone()))
            } else {
                todo!();
            }
        } else {
            self.as_word[word_len - 1].1 += 1;
            self.underlying *= self.gens[last_step.0].0.clone();
            Some((self.underlying.clone(), self.as_word.clone()))
        }
    }
}

mod test {

    #[test]
    fn mathieu() {
        use super::ExplicitlyGenerated;
        use crate::finset::from_cycle;
        use itertools::Itertools;
        use num::One;
        use permutations::Permutation;
        use std::ops::{DivAssign, Mul, MulAssign};

        #[repr(transparent)]
        #[derive(Clone, PartialEq, Eq, Debug)]
        struct S24(Permutation);

        impl Mul for S24 {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self::Output {
                Self(self.0 * rhs.0)
            }
        }

        impl MulAssign for S24 {
            fn mul_assign(&mut self, rhs: Self) {
                self.0 = self.0.clone() * rhs.0
            }
        }

        impl DivAssign for S24 {
            fn div_assign(&mut self, rhs: Self) {
                self.0 = self.0.clone() * rhs.0.inv()
            }
        }

        impl One for S24 {
            fn one() -> Self {
                Self(Permutation::identity(24))
            }
        }

        type M24 = ExplicitlyGenerated<S24>;
        let gen1 = S24(from_cycle(24, &(0..23).collect_vec()));
        let gen2 = S24(from_cycle(24, &[2, 6, 9, 16, 8])
            * from_cycle(24, &[3, 12, 13, 18, 4])
            * from_cycle(24, &[7, 17, 10, 11, 22])
            * from_cycle(24, &[14, 19, 21, 20, 15]));
        let gen3 = S24(Permutation::transposition(24, 0, 23)
            * Permutation::transposition(24, 1, 22)
            * Permutation::transposition(24, 2, 11)
            * Permutation::transposition(24, 3, 15)
            * Permutation::transposition(24, 4, 17)
            * Permutation::transposition(24, 5, 9)
            * Permutation::transposition(24, 6, 19)
            * Permutation::transposition(24, 7, 13)
            * Permutation::transposition(24, 8, 20)
            * Permutation::transposition(24, 10, 16)
            * Permutation::transposition(24, 12, 21)
            * Permutation::transposition(24, 14, 18));

        let iden = M24::new(
            vec![gen1.clone(), gen2.clone(), gen3.clone()],
            vec![Some(23), Some(5), Some(2)],
            S24(Permutation::identity(24)),
        );
        assert_eq!(iden.generator(0).underlying, gen1);
        assert_eq!(iden.generator(1).underlying, gen2);
        assert_eq!(iden.generator(2).underlying, gen3);
        assert_eq!(iden.generator(3).underlying, gen1);
        assert_eq!(iden.generator(4).underlying, gen2);
        assert_eq!(iden.generator(5).underlying, gen3);
        assert!(iden.commuting_gens.is_empty());
        let g1 = iden.generator(0);
        let g2 = iden.generator(1);
        assert_eq!(
            (g1.clone() * g1.clone()).underlying,
            gen1.clone() * gen1.clone()
        );
        assert_eq!(
            (g1.clone() * g2.clone()).underlying,
            gen1.clone() * gen2.clone()
        );
        assert_eq!(
            (g2.clone() * g1.clone()).underlying,
            gen2.clone() * gen1.clone()
        );
        let mut dummy = g2.clone() * g1.clone() * g2.clone() * g2.clone() * g1.clone();
        assert_eq!(
            dummy.underlying,
            gen2.clone() * gen1.clone() * gen2.clone() * gen2.clone() * gen1.clone()
        );
        assert_eq!(dummy.as_word, vec![(1, 1), (0, 1), (1, 2), (0, 1)]);
        let concern_idcs = dummy.condense_word(None);
        assert!(concern_idcs.is_empty());
        assert_eq!(dummy.as_word, vec![(1, 1), (0, 1), (1, 2), (0, 1)]);
        dummy /= dummy.clone();
        assert_eq!(dummy.as_word, vec![]);
        for (_as_s24, _as_word) in iden.take(0) {}
    }
}
