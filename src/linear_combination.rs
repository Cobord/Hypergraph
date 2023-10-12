use {
    num::{One, Zero},
    std::{
        collections::HashMap,
        fmt::Debug,
        hash::Hash,
        ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    },
};

/*
a formal linear combination of terms from Target with coefficients drawn from Coeffs
*/
#[repr(transparent)]
#[derive(PartialEq, Eq, Debug, Default, Clone)]
pub struct LinearCombination<Coeffs, Target: Eq + Hash>(HashMap<Target, Coeffs>);

impl<Coeffs, Target: Eq + Hash> FromIterator<(Target, Coeffs)>
    for LinearCombination<Coeffs, Target>
{
    fn from_iter<T: IntoIterator<Item = (Target, Coeffs)>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<Coeffs, Target: Eq + Hash> Add for LinearCombination<Coeffs, Target>
where
    Coeffs: Copy + AddAssign,
{
    /*
    add two formal sums
    */
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
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

impl<Coeffs, Target: Eq + Hash> AddAssign for LinearCombination<Coeffs, Target>
where
    Coeffs: Copy + AddAssign,
{
    /*
    add two formal sums
    */
    fn add_assign(&mut self, rhs: Self) {
        for (k, v) in rhs.0.into_iter() {
            self.0
                .entry(k)
                .and_modify(|self_val: &mut Coeffs| *self_val += v)
                .or_insert(v);
        }
    }
}

impl<Coeffs, Target: Eq + Hash> Sub for LinearCombination<Coeffs, Target>
where
    Coeffs: Copy + SubAssign + Neg<Output = Coeffs>,
{
    /*
    subtract two formal sums
    */
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
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

impl<Coeffs, Target: Eq + Hash> Neg for LinearCombination<Coeffs, Target>
where
    Coeffs: Copy + Neg<Output = Coeffs>,
{
    /*
    negate a formal sum
    */
    type Output = Self;

    fn neg(self) -> Self {
        let mut new_map = self.0;
        for val in new_map.values_mut() {
            *val = -*val;
        }
        Self(new_map)
    }
}

impl<Coeffs, Target: Eq + Hash> Mul<Coeffs> for LinearCombination<Coeffs, Target>
where
    Coeffs: Copy + MulAssign,
{
    /*
    multiply a formal sum by a coefficient
    */
    type Output = Self;

    fn mul(self, rhs: Coeffs) -> Self {
        let mut new_map = self.0;
        for val in new_map.values_mut() {
            *val *= rhs;
        }
        Self(new_map)
    }
}

impl<Coeffs, Target: Eq + Hash + Clone> Mul for LinearCombination<Coeffs, Target>
where
    Coeffs: Copy + AddAssign + Mul<Output = Coeffs> + MulAssign + One,
    Target: Mul<Output = Target>,
{
    /*
    multiply two formal sums provided the target has a multiplication operation
    */
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let mut ret_val = Self(HashMap::new());
        for (k1, c_k1) in self.0 {
            for (k2, c_k2) in &rhs.0 {
                ret_val += Self::singleton(k1.clone() * k2.clone()) * (c_k1 * (*c_k2));
            }
        }
        ret_val
    }
}

/*
This would be a conflicting implementation of Mul for two LinearCombination's
We like to choose the Target type so that it is a nice basis
which when multiplied doesn't produce a complicated linear combination
but instead just some Target again
For that reason, we choose the simpler implementation of Mul
instead of this more general one
*/
/*
impl<Coeffs: Copy, Target: Eq + Hash + Clone> Mul for LinearCombination<Coeffs, Target>
where
    Coeffs: AddAssign + Mul<Output = Coeffs> + MulAssign + One,
    Target: Mul<Output = LinearCombination<Coeffs,Target>>,
{
    /*
    multiply two formal sums provided the target has a multiplication operation
    that produces formal sums (usually singletons but does not have to be)
    */
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let mut ret_val = Self(HashMap::new());
        for (k1, c_k1) in self.0 {
            for (k2, c_k2) in &rhs.0 {
                ret_val += (k1.clone() * k2.clone()) * (c_k1 * (*c_k2));
            }
        }
        ret_val
    }
}
*/

impl<Coeffs, Target: Eq + Hash> MulAssign<Coeffs> for LinearCombination<Coeffs, Target>
where
    Coeffs: Copy + MulAssign,
{
    /*
    multiply a formal sum by a coefficient
    */
    fn mul_assign(&mut self, rhs: Coeffs) {
        for val in self.0.values_mut() {
            *val *= rhs;
        }
    }
}

impl<Coeffs, Target: Eq + Hash> LinearCombination<Coeffs, Target> {
    pub fn linear_combine<U, V, F>(
        &self,
        rhs: LinearCombination<Coeffs, U>,
        combiner: F,
    ) -> LinearCombination<Coeffs, V>
    where
        Coeffs: Copy + AddAssign + Mul<Output = Coeffs> + MulAssign + One,
        Target: Eq + Hash + Clone,
        U: Eq + Hash + Clone,
        V: Eq + Hash,
        F: Fn(Target, U) -> V,
    {
        /*
        given a linear combination of T's and a linear combination of U's
        and an operation that acts like multiplication of T and U to produce V
        perform the multiplication
        */
        let mut ret_val = LinearCombination(HashMap::new());
        for (k1, c_k1) in &self.0 {
            for (k2, c_k2) in &rhs.0 {
                ret_val += LinearCombination::singleton(combiner(k1.clone(), k2.clone()))
                    * (*c_k1 * (*c_k2));
            }
        }
        ret_val
    }

    pub fn change_coeffs<F>(&mut self, coeff_changer: F)
    where
        Coeffs: Copy,
        F: Fn(Coeffs) -> Coeffs,
    {
        /*
        change all the coefficients by a function
        should be by some endomorphism of a coefficient ring
        so that this is the induced on endomorphism on R[Target]
        */
        for val in self.0.values_mut() {
            *val = coeff_changer(*val);
        }
    }

    pub fn all_terms_satisfy<F>(&self, term_predicate: F) -> bool
    where
        F: Fn(&Target) -> bool,
    {
        /*
        do all the terms without their coefficients
        satisfy some predicate
        */
        self.0.keys().all(term_predicate)
    }
}

impl<Coeffs, Target: Eq + Hash> LinearCombination<Coeffs, Target>
where
    Coeffs: One,
{
    pub fn singleton(t: Target) -> Self {
        /*
        a single term with coefficient 1
        */
        Self([(t, <_>::one())].into())
    }
}

impl<Coeffs: Zero, Target: Eq + Hash> LinearCombination<Coeffs, Target> {
    pub fn simplify(&mut self) {
        /*
        get rid of all the terms that have 0 coefficient
        */
        self.0.retain(|_, v| !v.is_zero());
    }
}

impl<Coeffs, Target: Clone + Eq + Hash> LinearCombination<Coeffs, Target> {
    pub fn inj_linearly_extend<Target2: Eq + Hash, F>(
        &self,
        injection: F,
    ) -> LinearCombination<Coeffs, Target2>
    where
        F: Fn(Target) -> Target2,
        Coeffs: Copy,
    {
        /*
        do an injective map T1->T2 to induce a map
        R[T1] -> R[T2]
        */
        let mut new_map = HashMap::with_capacity(self.0.len());
        for (k, v) in self.0.iter() {
            let new_key = injection(k.clone());
            let old_val = new_map.insert(new_key, *v);
            assert_eq!(
                old_val.map(|_| 0),
                None,
                "The function called injection should have been injective"
            );
        }
        LinearCombination(new_map)
    }

    pub fn linearly_extend<Target2: Eq + Hash, F>(&self, f: F) -> LinearCombination<Coeffs, Target2>
    where
        F: Fn(Target) -> Target2,
        Coeffs: Copy + Add<Output = Coeffs>,
    {
        /*
        do a map T1->T2 (but this time not necessarily injective) to induce a map
        R[T1] -> R[T2]
        */
        let mut new_map = HashMap::with_capacity(self.0.len());
        for (k, v) in self.0.iter() {
            let new_key = f(k.clone());
            if let Some(old_val) = new_map.get(&new_key) {
                new_map.insert(new_key, *old_val + *v);
            } else {
                new_map.insert(new_key, *v);
            }
        }
        LinearCombination(new_map)
    }
}

mod test {

    #[test]
    fn adding() {
        use super::LinearCombination;
        let one_a = LinearCombination::singleton("a".to_string());
        let two_b = LinearCombination::singleton("b".to_string()) * 2;
        let one_a_plus_two_b = one_a.clone() + two_b.clone();
        let two_b_plus_one_a = two_b + one_a;
        assert_eq!(one_a_plus_two_b, two_b_plus_one_a);
        let mut zeroed = one_a_plus_two_b - two_b_plus_one_a;
        zeroed.simplify();
        assert!(zeroed.0.is_empty());
    }
}
