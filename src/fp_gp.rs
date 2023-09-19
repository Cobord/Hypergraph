use std::ops::{DivAssign, MulAssign};

use num::One;

use itertools::{
    FoldWhile::{Continue, Done},
    Itertools,
};

pub trait FinitelyPresentedGroup: MulAssign + One + DivAssign {
    fn generator(n: usize) -> Self;
    fn num_generators() -> usize;
}

pub struct FinitelyPresentedWords<T>
where
    T: FinitelyPresentedGroup,
{
    current_word: Vec<usize>,
    current_element: T,
    num_generators: usize,
}

impl<T> FinitelyPresentedWords<T>
where
    T: FinitelyPresentedGroup,
{
    #[allow(dead_code)]
    pub fn new() -> Self {
        let current_element = T::one();
        let num_generators = T::num_generators();
        Self {
            current_word: vec![],
            current_element,
            num_generators,
        }
    }
}

/*
iterate through the words in num_generators() letters
giving their corresponding group elements
the iterator does not care whether they were seen before or not
*/
impl<T> Iterator for FinitelyPresentedWords<T>
where
    T: FinitelyPresentedGroup + Clone,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let num_generators = self.num_generators;
        let to_yield = Some(self.current_element.clone());
        if let Some(current_last) = self.current_word.pop() {
            if current_last < num_generators - 1 {
                self.current_word.push(current_last + 1);
                self.current_element /= T::generator(current_last);
                self.current_element *= T::generator(current_last + 1);
            } else if self.current_word.iter().all(|z| *z + 1 == num_generators) {
                if num_generators > 1 {
                    self.current_word = vec![0; self.current_word.len() + 2];
                    self.current_element = self
                        .current_word
                        .iter()
                        .map(|z| T::generator(*z))
                        .fold(T::one(), |acc, x| acc * x);
                } else {
                    self.current_word.push(0);
                    self.current_word.push(0);
                    self.current_element *= T::generator(0);
                }
            } else {
                self.current_word.push(current_last);
                let len_word = self.current_word.len();
                let mut old_suffix = add_one(&mut self.current_word, num_generators);
                let suffix_length_changed = old_suffix.len();
                for _ in 0..suffix_length_changed {
                    let current_last = old_suffix.pop().unwrap();
                    self.current_element /= T::generator(current_last);
                }
                let incremented_letter_idx = len_word - suffix_length_changed - 1;
                let incremented_letter = self.current_word[incremented_letter_idx];
                self.current_element /= T::generator(incremented_letter - 1);
                self.current_element *= T::generator(incremented_letter);
                for idx in 0..suffix_length_changed {
                    let idx_in_word = len_word - suffix_length_changed + idx;
                    let current_last = self.current_word[idx_in_word];
                    self.current_element *= T::generator(current_last);
                }
            }
        } else if num_generators > 0 {
            self.current_word.push(0);
            self.current_element = T::generator(0);
        } else {
            panic!("0 generators not allowed")
        }
        to_yield
    }
}

fn add_one(current_word: &mut Vec<usize>, base: usize) -> Vec<usize> {
    let count_999s = current_word
        .iter()
        .rev()
        .fold_while(0, |acc, x| {
            if *x == base - 1 {
                Continue(acc + 1)
            } else {
                Done(acc)
            }
        })
        .into_inner();
    let suffix_start = current_word.len() - count_999s;
    let old_suffix = current_word.split_off(suffix_start);
    assert_eq!(old_suffix, vec![base - 1; count_999s]);
    let my_len = current_word.len();
    current_word[my_len - 1] += 1;
    current_word.extend(vec![0; count_999s]);
    old_suffix
}

mod test {

    #[test]
    fn integers() {
        /*
        iterate through the words in one letter by length
        giving their group elements in Z
        the letter representing 1
        */
        use super::{FinitelyPresentedGroup, FinitelyPresentedWords};
        use num::One;
        use std::ops::{DivAssign, Mul, MulAssign};
        #[derive(Clone, Debug)]
        struct Z(u16);
        impl MulAssign for Z {
            fn mul_assign(&mut self, rhs: Self) {
                self.0 += rhs.0;
            }
        }
        impl Mul for Z {
            type Output = Z;

            fn mul(self, rhs: Self) -> Self::Output {
                Z(self.0 + rhs.0)
            }
        }
        impl DivAssign for Z {
            fn div_assign(&mut self, rhs: Self) {
                self.0 -= rhs.0;
            }
        }
        impl One for Z {
            fn one() -> Self {
                Z(0)
            }
        }
        impl FinitelyPresentedGroup for Z {
            fn generator(_: usize) -> Self {
                Z(1)
            }

            fn num_generators() -> usize {
                1
            }
        }

        let gen = FinitelyPresentedWords::<Z>::new();
        for (idx, current) in gen.take(10).enumerate() {
            assert_eq!(current.0 as usize, idx);
        }
    }

    #[test]
    fn z2() {
        /*
        iterate through the words in two letters by length
        giving their group elements in Z^2
        the two letters representing (1,0) and (0,1) respectively
        gen does not care whether they were seen before or not,
        but because these are Hashable, can filter using the unique method
        */
        use super::{FinitelyPresentedGroup, FinitelyPresentedWords};
        use itertools::Itertools;
        use num::One;
        use std::ops::{DivAssign, Mul, MulAssign};
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        struct Z2(u16, u16);
        impl MulAssign for Z2 {
            fn mul_assign(&mut self, rhs: Self) {
                self.0 += rhs.0;
                self.1 += rhs.1;
            }
        }
        impl Mul for Z2 {
            type Output = Z2;

            fn mul(self, rhs: Self) -> Self::Output {
                Z2(self.0 + rhs.0, self.1 + rhs.1)
            }
        }
        impl DivAssign for Z2 {
            fn div_assign(&mut self, rhs: Self) {
                self.0 -= rhs.0;
                self.1 -= rhs.1;
            }
        }
        impl One for Z2 {
            fn one() -> Self {
                Z2(0, 0)
            }
        }
        impl FinitelyPresentedGroup for Z2 {
            fn generator(gen: usize) -> Self {
                if gen % 2 == 0 {
                    Z2(1, 0)
                } else {
                    Z2(0, 1)
                }
            }

            fn num_generators() -> usize {
                2
            }
        }

        let gen = FinitelyPresentedWords::<Z2>::new();
        let expected = [
            Z2(0, 0),
            Z2(1, 0),
            Z2(0, 1),
            Z2(2, 0),
            Z2(1, 1),
            Z2(0, 2),
            Z2(3, 0),
            Z2(2, 1),
            Z2(1, 2),
            Z2(0, 3),
        ];
        let num_expected = expected.len();
        for (idx, current) in gen.unique().take(num_expected).enumerate() {
            assert_eq!(current, expected[idx], "on idx {}", idx);
        }
    }

    #[test]
    fn free_z2_3() {
        /*
        iterate through the words in letters a,b,c by length
        giving their group elements in Z_2 \star Z_2 \star Z_2
        regardless of whether they were seen before as shorter words or not
        */
        use super::{FinitelyPresentedGroup, FinitelyPresentedWords};
        use crate::free_gp::{FreeGroup, FreeZ2_3};
        let a = FreeGroup::<FreeZ2_3>::generator(0);
        let b = FreeGroup::<FreeZ2_3>::generator(1);
        let c = FreeGroup::<FreeZ2_3>::generator(2);
        let id = FreeGroup::<FreeZ2_3>::new(vec![]);

        let gen = FinitelyPresentedWords::<FreeGroup<FreeZ2_3>>::new();
        let expected = [
            id.clone(),
            a.clone(),
            b.clone(),
            c.clone(),
            id.clone(),
            a.clone() * b.clone(),
            a.clone() * c.clone(),
            b.clone() * a.clone(),
            id.clone(),
            b.clone() * c.clone(),
            c.clone() * a.clone(),
            c.clone() * b.clone(),
            id.clone(),
            a.clone(),
            b.clone(),
            c.clone(),
            a.clone() * b.clone() * a.clone(),
            a.clone(),
            a.clone() * b.clone() * c.clone(),
            a.clone() * c.clone() * a.clone(),
            a.clone() * c.clone() * b.clone(),
            a.clone(),
        ];
        let num_expected = expected.len();
        for (idx, current) in gen.take(num_expected).enumerate() {
            assert_eq!(current, expected[idx], "on idx {}", idx);
        }
    }
}
