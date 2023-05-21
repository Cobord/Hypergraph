use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use num::{One, Zero};

#[repr(transparent)]
pub struct LinearCombination<Coeffs: Copy, Target: Eq + Hash>(HashMap<Target, Coeffs>);

impl<Coeffs: Copy, Target: Eq + Hash> Clone for LinearCombination<Coeffs, Target>
where
    Target: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<Coeffs: Copy, Target: Eq + Hash> PartialEq for LinearCombination<Coeffs, Target>
where
    Coeffs: Eq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<Coeffs: Copy, Target: Eq + Hash> Debug for LinearCombination<Coeffs, Target>
where
    Coeffs: Debug,
    Target: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("LinearCombination").field(&self.0).finish()
    }
}

impl<Coeffs: Copy, Target: Eq + Hash> Add for LinearCombination<Coeffs, Target>
where
    Coeffs: AddAssign,
{
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut new_map = self.0;
        for (k, v) in rhs.0.into_iter() {
            new_map
                .entry(k)
                .and_modify(|self_val: &mut Coeffs| *self_val += v)
                .or_insert(v);
        }
        Self(new_map)
    }
}

impl<Coeffs: Copy, Target: Eq + Hash> AddAssign for LinearCombination<Coeffs, Target>
where
    Coeffs: AddAssign,
{
    fn add_assign(&mut self, rhs: Self) {
        for (k, v) in rhs.0.into_iter() {
            self.0
                .entry(k)
                .and_modify(|self_val: &mut Coeffs| *self_val += v)
                .or_insert(v);
        }
    }
}

impl<Coeffs: Copy, Target: Eq + Hash> Sub for LinearCombination<Coeffs, Target>
where
    Coeffs: SubAssign + Neg<Output = Coeffs>,
{
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut new_map = self.0;
        for (k, v) in rhs.0.into_iter() {
            new_map
                .entry(k)
                .and_modify(|self_val: &mut Coeffs| *self_val -= v)
                .or_insert(-v);
        }
        Self(new_map)
    }
}

impl<Coeffs: Copy, Target: Eq + Hash> Neg for LinearCombination<Coeffs, Target>
where
    Coeffs: Neg<Output = Coeffs>,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        let mut new_map = self.0;
        for (_, val) in new_map.iter_mut() {
            *val = -*val;
        }
        Self(new_map)
    }
}

impl<Coeffs: Copy, Target: Eq + Hash> Mul<Coeffs> for LinearCombination<Coeffs, Target>
where
    Coeffs: MulAssign,
{
    type Output = Self;

    fn mul(self, rhs: Coeffs) -> Self::Output {
        let mut new_map = self.0;
        for (_, val) in new_map.iter_mut() {
            *val *= rhs;
        }
        Self(new_map)
    }
}

impl<Coeffs: Copy, Target: Eq + Hash + Clone> Mul for LinearCombination<Coeffs, Target>
where
    Coeffs: AddAssign + Mul<Output = Coeffs> + MulAssign + One,
    Target: Mul<Output = Target>,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut ret_val = Self(HashMap::new());
        for (k1, c_k1) in self.0 {
            for (k2, c_k2) in &rhs.0 {
                ret_val += LinearCombination::<Coeffs, Target>::singleton(k1.clone() * k2.clone())
                    * (c_k1 * (*c_k2));
            }
        }
        ret_val
    }
}

impl<Coeffs: Copy, Target: Eq + Hash> MulAssign<Coeffs> for LinearCombination<Coeffs, Target>
where
    Coeffs: MulAssign,
{
    fn mul_assign(&mut self, rhs: Coeffs) {
        for (_, val) in self.0.iter_mut() {
            *val *= rhs;
        }
    }
}

pub fn linear_combine<Coeffs, T, U, V, F>(
    me: LinearCombination<Coeffs, T>,
    rhs: LinearCombination<Coeffs, U>,
    combiner: F,
) -> LinearCombination<Coeffs, V>
where
    Coeffs: Copy + AddAssign + Mul<Output = Coeffs> + MulAssign + One,
    T: Eq + Hash + Clone,
    U: Eq + Hash + Clone,
    V: Eq + Hash,
    F: Fn(T, U) -> V,
{
    let mut ret_val = LinearCombination::<Coeffs, V>(HashMap::new());
    for (k1, c_k1) in me.0 {
        for (k2, c_k2) in &rhs.0 {
            ret_val += LinearCombination::<Coeffs, V>::singleton(combiner(k1.clone(), k2.clone()))
                * (c_k1 * (*c_k2));
        }
    }
    ret_val
}

impl<Coeffs: Copy, Target: Eq + Hash> LinearCombination<Coeffs, Target>
where
    Coeffs: One,
{
    pub fn singleton(t: Target) -> Self {
        let one_c = Coeffs::one();
        let mut my_map = HashMap::new();
        my_map.insert(t, one_c);
        Self(my_map)
    }

    pub fn change_coeffs<F>(&mut self, coeff_changer: F)
    where
        F: Fn(Coeffs) -> Coeffs,
    {
        for (_, val) in self.0.iter_mut() {
            *val = coeff_changer(*val);
        }
    }

    pub fn all_terms_satisfy<F>(&self, is_non_crossing: F) -> bool
    where
        F: Fn(&Target) -> bool,
    {
        for (term, _) in self.0.iter() {
            if !is_non_crossing(term) {
                return false;
            }
        }
        true
    }
}

pub fn simplify<Coeffs: Copy, Target: Eq + Hash>(me: &mut LinearCombination<Coeffs, Target>)
where
    Coeffs: Zero + Eq,
{
    me.0.retain(|_, v| *v != Coeffs::zero());
}

pub fn inj_linearly_extend<Coeffs: Copy, Target: Eq + Hash + Clone, Target2: Eq + Hash, F>(
    me: &LinearCombination<Coeffs, Target>,
    injection: F,
) -> LinearCombination<Coeffs, Target2>
where
    F: Fn(Target) -> Target2,
{
    let mut new_map = HashMap::with_capacity(me.0.len());
    for (k, v) in me.0.iter() {
        let new_key = injection(k.clone());
        let old_val = new_map.insert(new_key, *v);
        assert_eq!(
            old_val.map(|_| 0),
            None,
            "The function called injection should have been injective"
        );
    }
    LinearCombination::<Coeffs, Target2>(new_map)
}

pub fn linearly_extend<Coeffs: Copy, Target: Eq + Hash + Clone, Target2: Eq + Hash, F>(
    me: &LinearCombination<Coeffs, Target>,
    my_f: F,
) -> LinearCombination<Coeffs, Target2>
where
    F: Fn(Target) -> Target2,
    Coeffs: Add<Output = Coeffs>,
{
    let mut new_map = HashMap::with_capacity(me.0.len());
    for (k, v) in me.0.iter() {
        let new_key = my_f(k.clone());
        if let Some(old_val) = new_map.get(&new_key) {
            new_map.insert(new_key, *old_val + *v);
        } else {
            new_map.insert(new_key, *v);
        }
    }
    LinearCombination::<Coeffs, Target2>(new_map)
}

mod test {

    #[test]
    fn adding() {
        use super::{simplify, LinearCombination};
        let one_a = LinearCombination::<i32, String>::singleton("a".to_string());
        let two_b = LinearCombination::<i32, String>::singleton("b".to_string()) * 2;
        let one_a_plus_two_b = one_a.clone() + two_b.clone();
        let two_b_plus_one_a = two_b + one_a;
        assert_eq!(one_a_plus_two_b, two_b_plus_one_a);
        let mut zeroed = one_a_plus_two_b - two_b_plus_one_a;
        simplify(&mut zeroed);
        assert!(zeroed.0.is_empty());
    }
}