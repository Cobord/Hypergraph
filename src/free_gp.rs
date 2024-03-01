use num::One;
use std::ops::{DivAssign, Mul, MulAssign};

use crate::fp_gp::FinitelyPresentedGroup;

type Power = usize;

/*
impl this on an enum
each of the variants gives a generator of some order
the overall group will be Z_{n_1} \star ... Z_{n_m}
*/
pub trait FreeGenerator: Eq + Clone {
    fn gen_order(&self) -> Power;
    fn num_generators() -> usize;
    fn generator(n: usize) -> Self;
}

/*
e.g. (a,1),(b,2),(a,3) representing a^1*b^2*a^3
*/
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FreeGroup<Gen>
where
    Gen: FreeGenerator,
{
    word: Vec<(Gen, Power)>,
}

impl<Gen> FreeGroup<Gen>
where
    Gen: FreeGenerator,
{
    fn validate(&self) {
        for (idx, cur_window) in self.word.windows(2).enumerate() {
            let p1 = &cur_window[0];
            let p2 = &cur_window[1];
            assert!(
                p1.0 != p2.0,
                "Neighboring generator powers must be different"
            );
            if idx == 0 {
                assert!(p1.1 > 0, "The powers must be greater than 0");
                assert!(
                    p1.1 < p1.0.gen_order(),
                    "The powers must be less than the order of that generator"
                );
            }
            assert!(p2.1 > 0, "The powers must be greater than 0");
            assert!(
                p2.1 < p2.0.gen_order(),
                "The powers must be less than the order of that generator"
            );
        }
    }

    #[allow(dead_code)]
    pub fn new(word: Vec<(Gen, usize)>) -> Self {
        let to_return = Self { word };
        to_return.validate();
        to_return
    }

    fn word_length_ub(&self) -> usize {
        self.word.iter().fold(0, |acc, x| acc + x.1)
    }
}

impl<Gen> Mul for FreeGroup<Gen>
where
    Gen: FreeGenerator,
{
    type Output = Self;

    #[allow(clippy::unnecessary_cast)]
    fn mul(self, rhs: Self) -> Self::Output {
        if self.word_length_ub() == 0 {
            return rhs;
        }
        if rhs.word_length_ub() == 0 {
            return self;
        }
        let (self_last_gen, self_last_pow) = &self.word[self.word.len() - 1];
        let (rhs_first_gen, rhs_first_pow) = &rhs.word[0];
        if *self_last_gen != *rhs_first_gen {
            let mut rhs_copy = rhs.word;
            let mut word = self.word;
            word.append(&mut rhs_copy);
            Self { word }
        } else if self_last_pow + rhs_first_pow != self_last_gen.gen_order() {
            let mut rhs_copy = rhs.word;
            rhs_copy[0].1 += self_last_pow;
            rhs_copy[0].1 %= self_last_gen.gen_order() as usize;
            let mut word = self.word.clone();
            let _ = word.pop();
            word.append(&mut rhs_copy);
            Self { word }
        } else {
            let mut self_copy = self.clone();
            let _ = self_copy.word.pop();
            let mut rhs_copy = rhs.clone();
            let _ = rhs_copy.word.drain(0..1);
            self_copy * rhs_copy
        }
    }
}

impl<Gen> One for FreeGroup<Gen>
where
    Gen: FreeGenerator,
{
    fn one() -> Self {
        Self { word: vec![] }
    }
}

impl<Gen> MulAssign for FreeGroup<Gen>
where
    Gen: FreeGenerator,
{
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<Gen> DivAssign for FreeGroup<Gen>
where
    Gen: FreeGenerator,
{
    #[allow(clippy::suspicious_op_assign_impl)]
    fn div_assign(&mut self, rhs: Self) {
        let mut rhs_inv = rhs;
        rhs_inv.word.reverse();
        rhs_inv.word.iter_mut().for_each(|z| {
            z.1 = z.0.gen_order() - z.1;
        });
        *self *= rhs_inv;
    }
}

impl<Gen> FinitelyPresentedGroup for FreeGroup<Gen>
where
    Gen: FreeGenerator,
{
    fn generator(n: usize) -> Self {
        let singleton = Gen::generator(n);
        Self {
            word: vec![(singleton, 1)],
        }
    }

    fn num_generators() -> usize {
        Gen::num_generators()
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum FreeZ2_3 {
    A,
    B,
    C,
}

impl FreeGenerator for FreeZ2_3 {
    fn gen_order(&self) -> Power {
        2
    }

    fn num_generators() -> usize {
        3
    }

    fn generator(n: usize) -> Self {
        match n % 3 {
            0 => Self::A,
            1 => Self::B,
            2 => Self::C,
            _ => unreachable!("modulo 3 not giving 0,1,2"),
        }
    }
}
