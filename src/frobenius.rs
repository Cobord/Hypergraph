use permutations::Permutation;
use std::convert::identity;
use std::fmt::Debug;

use crate::category::{ComposableMutating, HasIdentity};
use crate::finset::Decomposition;
use crate::monoidal::{Monoidal, MonoidalMutatingMorphism};
use crate::symmetric_monoidal::SymmetricMonoidalMutatingMorphism;
use crate::utils::in_place_permute;

#[derive(PartialEq, Eq, Clone)]
pub enum FrobeniusOperation<Lambda: Eq + Copy, BlackBoxLabel: Eq + Copy> {
    Unit(Lambda),
    Multiplication(Lambda),
    Comultiplication(Lambda),
    Counit(Lambda),
    Identity(Lambda),
    SymmetricBraiding(Lambda, Lambda),
    UnSpecifiedBox(BlackBoxLabel, Vec<Lambda>, Vec<Lambda>),
}

impl<Lambda, BlackBoxLabel> FrobeniusOperation<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy,
    BlackBoxLabel: Eq + Copy,
{
    fn source_size(&self) -> usize {
        match self {
            Self::Unit(_) => 0,
            Self::Comultiplication(_) | Self::Counit(_) | Self::Identity(_) => 1,
            Self::Multiplication(_) | Self::SymmetricBraiding(_, _) => 2,
            Self::UnSpecifiedBox(_, srcs, _) => srcs.len(),
        }
    }

    fn target_size(&self) -> usize {
        match self {
            Self::Counit(_) => 0,
            Self::Unit(_) | Self::Multiplication(_) | Self::Identity(_) => 1,
            Self::Comultiplication(_) | Self::SymmetricBraiding(_, _) => 2,
            Self::UnSpecifiedBox(_, _, tgts) => tgts.len(),
        }
    }

    fn source_types(&self) -> Vec<Lambda> {
        match self {
            Self::Unit(_) => vec![],
            Self::Multiplication(z) => vec![*z, *z],
            Self::Comultiplication(z) | Self::Counit(z) | Self::Identity(z) => vec![*z],
            Self::SymmetricBraiding(z, w) => vec![*z, *w],
            Self::UnSpecifiedBox(_, srcs, _) => srcs.clone(),
        }
    }

    fn target_types(&self) -> Vec<Lambda> {
        match self {
            Self::Unit(z) | Self::Identity(z) | Self::Multiplication(z) => vec![*z],
            Self::Comultiplication(z) => vec![*z, *z],
            Self::Counit(_) => vec![],
            Self::SymmetricBraiding(z, w) => vec![*w, *z],
            Self::UnSpecifiedBox(_, _, tgts) => tgts.clone(),
        }
    }

    fn hflip<F>(&mut self, black_box_changer: F)
    where
        F: Fn(BlackBoxLabel) -> BlackBoxLabel,
    {
        *self = match self {
            Self::Unit(z) => Self::Counit(*z),
            Self::Multiplication(z) => Self::Comultiplication(*z),
            Self::Comultiplication(z) => Self::Multiplication(*z),
            Self::Counit(z) => Self::Unit(*z),
            Self::Identity(z) => Self::Identity(*z),
            Self::SymmetricBraiding(z, w) => Self::SymmetricBraiding(*w, *z),
            Self::UnSpecifiedBox(label, srcs, tgts) => {
                Self::UnSpecifiedBox(black_box_changer(*label), tgts.clone(), srcs.clone())
            }
        };
    }
}

#[derive(PartialEq, Eq, Clone)]
struct FrobeniusBlock<Lambda: Eq + Copy, BlackBoxLabel: Eq + Copy> {
    op: FrobeniusOperation<Lambda, BlackBoxLabel>,
    source_side_placement: usize,
    target_side_placement: usize,
}

impl<Lambda, BlackBoxLabel> FrobeniusBlock<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy,
    BlackBoxLabel: Eq + Copy,
{
    fn new(
        op: FrobeniusOperation<Lambda, BlackBoxLabel>,
        source_side_placement: usize,
        target_side_placement: usize,
    ) -> Self {
        Self {
            op,
            source_side_placement,
            target_side_placement,
        }
    }

    fn source_size(&self) -> usize {
        self.op.source_size()
    }

    #[allow(dead_code)]
    fn source_idces(&self) -> Vec<usize> {
        (0..self.source_size())
            .map(|z| z + self.source_side_placement)
            .collect()
    }

    fn target_size(&self) -> usize {
        self.op.target_size()
    }

    #[allow(dead_code)]
    fn target_idces(&self) -> Vec<usize> {
        (0..self.target_size())
            .map(|z| z + self.target_side_placement)
            .collect()
    }

    fn hflip<F>(&mut self, black_box_changer: F)
    where
        F: Fn(BlackBoxLabel) -> BlackBoxLabel,
    {
        self.op.hflip(black_box_changer);
        let temp = self.target_side_placement;
        self.source_side_placement = self.target_side_placement;
        self.target_side_placement = temp;
    }
}

#[derive(PartialEq, Eq, Clone)]
struct FrobeniusLayer<Lambda: Eq + Copy, BlackBoxLabel: Eq + Copy> {
    blocks: Vec<FrobeniusBlock<Lambda, BlackBoxLabel>>,
    left_type: Vec<Lambda>,
    right_type: Vec<Lambda>,
}

impl<Lambda, BlackBoxLabel> FrobeniusLayer<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy,
    BlackBoxLabel: Eq + Copy,
{
    pub fn new() -> Self {
        Self {
            blocks: vec![],
            left_type: vec![],
            right_type: vec![],
        }
    }

    fn hflip<F>(&mut self, black_box_changer: &F)
    where
        F: Fn(BlackBoxLabel) -> BlackBoxLabel,
    {
        for block in self.blocks.iter_mut() {
            block.hflip(black_box_changer);
        }
        let temp = self.left_type.clone();
        self.left_type = self.right_type.clone();
        self.right_type = temp;
    }

    pub fn append_block(&mut self, op: FrobeniusOperation<Lambda, BlackBoxLabel>) {
        let source_side_placement = self.left_type.len();
        let target_side_placement = self.right_type.len();
        self.left_type.extend(op.source_types());
        self.right_type.extend(op.target_types());
        self.blocks.push(FrobeniusBlock::new(
            op,
            source_side_placement,
            target_side_placement,
        ));
    }
}

impl<Lambda, BlackBoxLabel> HasIdentity<Vec<Lambda>> for FrobeniusLayer<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy,
    BlackBoxLabel: Eq + Copy,
{
    fn identity(on_type: &Vec<Lambda>) -> Self {
        let mut answer = FrobeniusLayer::new();
        for cur_type in on_type {
            answer.append_block(FrobeniusOperation::Identity(*cur_type));
        }
        answer
    }
}

impl<Lambda, BlackBoxLabel> Monoidal for FrobeniusLayer<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy,
    BlackBoxLabel: Eq + Copy,
{
    fn monoidal(&mut self, other: Self) {
        for new_op in other.blocks {
            self.append_block(new_op.op);
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct FrobeniusMorphism<Lambda: Eq + Copy + Debug, BlackBoxLabel: Eq + Copy> {
    layers: Vec<FrobeniusLayer<Lambda, BlackBoxLabel>>,
}

impl<Lambda: Eq + Copy + Debug, BlackBoxLabel: Eq + Copy>
    From<FrobeniusOperation<Lambda, BlackBoxLabel>> for FrobeniusMorphism<Lambda, BlackBoxLabel>
{
    fn from(op: FrobeniusOperation<Lambda, BlackBoxLabel>) -> Self {
        let mut answer_layer = FrobeniusLayer::new();
        answer_layer.append_block(op);
        let mut answer = FrobeniusMorphism::new();
        let _ = answer.append_layer(answer_layer);
        answer
    }
}

impl<Lambda, BlackBoxLabel> FrobeniusMorphism<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy + Debug,
    BlackBoxLabel: Eq + Copy,
{
    pub fn new() -> Self {
        Self { layers: vec![] }
    }

    #[allow(dead_code)]
    pub fn depth(&self) -> usize {
        self.layers.len()
    }

    fn append_layer(
        &mut self,
        next_layer: FrobeniusLayer<Lambda, BlackBoxLabel>,
    ) -> Result<(), String> {
        if let Some(v) = self.layers.pop() {
            if v.right_type != next_layer.left_type {
                return Err("type mismatch in frobenius morphims composition".to_string());
            }
            self.layers.push(v);
        }
        self.layers.push(next_layer);
        Ok(())
    }

    fn hflip<F>(&mut self, black_box_changer: &F)
    where
        F: Fn(BlackBoxLabel) -> BlackBoxLabel,
    {
        for layer in self.layers.iter_mut() {
            layer.hflip(black_box_changer);
        }
        self.layers.reverse();
    }
}

impl<Lambda, BlackBoxLabel> HasIdentity<Vec<Lambda>> for FrobeniusMorphism<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy + Debug,
    BlackBoxLabel: Eq + Copy,
{
    fn identity(on_this: &Vec<Lambda>) -> Self {
        Self {
            layers: vec![<_>::identity(on_this)],
        }
    }
}

impl<Lambda, BlackBoxLabel> Monoidal for FrobeniusMorphism<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy + Debug,
    BlackBoxLabel: Eq + Copy,
{
    fn monoidal(&mut self, other: Self) {
        let self_len = self.layers.len();
        let others_len = other.layers.len();
        let mut last_other_type: Vec<Lambda> = vec![];
        let mut last_self_type: Vec<Lambda> = vec![];
        for (n, cur_self_layer) in self.layers.iter_mut().enumerate() {
            last_self_type = cur_self_layer.right_type.clone();
            if n < other.layers.len() {
                last_other_type = other.layers[n].right_type.clone();
                cur_self_layer.monoidal(other.layers[n].clone());
            } else {
                cur_self_layer.monoidal(<_>::identity(&last_other_type));
            }
        }
        for n in self_len..others_len {
            let mut new_layer = FrobeniusLayer::identity(&last_self_type);
            new_layer.monoidal(other.layers[n].clone());
            let _ = self.append_layer(new_layer);
        }
    }
}

impl<Lambda, BlackBoxLabel> ComposableMutating<Vec<Lambda>>
    for FrobeniusMorphism<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy + Debug,
    BlackBoxLabel: Eq + Copy,
{
    fn composable(&self, other: &Self) -> Result<(), String> {
        if self.layers.is_empty() || other.layers.is_empty() {
            if self.layers.is_empty() && other.layers.is_empty() {
                return Ok(());
            } else if self.layers.is_empty() {
                let other_interface = &other.layers[0].left_type;
                if other_interface.is_empty() {
                    return Ok(());
                } else {
                    return Err("Mismatch in cardinalities of common interface".to_string());
                }
            } else {
                let self_interface = &self.layers.last().unwrap().right_type;
                if self_interface.is_empty() {
                    return Ok(());
                } else {
                    return Err("Mismatch in cardinalities of common interface".to_string());
                }
            }
        }
        let self_interface = &self.layers.last().unwrap().right_type;
        let other_interface = &other.layers[0].left_type;
        if self_interface.len() != other_interface.len() {
            Err("Mismatch in cardinalities of common interface".to_string())
        } else if self_interface != other_interface {
            for idx in 0..self_interface.len() {
                let w1 = self_interface[idx];
                let w2 = other_interface[idx];
                if w1 != w2 {
                    return Err(format!(
                        "Mismatch in labels of common interface. At some index there was {:?} vs {:?}",
                        w1, w2
                    ));
                }
            }
            Err("Mismatch in labels of common interface at some unknown index.".to_string())
        } else {
            Ok(())
        }
    }

    fn compose(&mut self, other: Self) -> Result<(), String> {
        for next_layer in other.layers {
            self.append_layer(next_layer)?;
        }
        Ok(())
    }

    fn domain(&self) -> Vec<Lambda> {
        self.layers
            .first()
            .map(|x| x.left_type.clone())
            .unwrap_or_default()
    }

    fn codomain(&self) -> Vec<Lambda> {
        self.layers
            .last()
            .map(|x| x.right_type.clone())
            .unwrap_or_default()
    }
}

impl<Lambda, BlackBoxLabel> MonoidalMutatingMorphism<Vec<Lambda>>
    for FrobeniusMorphism<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy + Debug,
    BlackBoxLabel: Eq + Copy,
{
}

impl<Lambda, BlackBoxLabel> SymmetricMonoidalMutatingMorphism<Lambda>
    for FrobeniusMorphism<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy + Debug,
    BlackBoxLabel: Eq + Copy,
{
    fn permute_side(&mut self, p: &permutations::Permutation, of_codomain: bool) {
        if of_codomain {
            assert_eq!(p.len(), self.codomain().len());
            let p_frob = Self::from_permutation(p.clone(), &self.codomain(), true);
            self.compose(p_frob).unwrap();
            todo!("might be p.inv() instead")
        } else {
            self.hflip(&identity);
            self.permute_side(&p.inv(), true);
            self.hflip(&identity)
        }
    }

    fn from_permutation(
        p: permutations::Permutation,
        types: &[Lambda],
        types_as_on_domain: bool,
    ) -> Self {
        if !types_as_on_domain {
            let mut answer = Self::from_permutation(p.inv(), types, true);
            answer.hflip(&identity);
            return answer;
        }

        if p == Permutation::identity(p.len()) {
            return Self::identity(&types.to_vec());
        }
        let mut types_now = types.to_vec();
        let mut p_remaining = p.clone();
        let mut first_layer = Self::new();
        for idx in (0..p_remaining.len() - 1).step_by(2) {
            let idx_goes = p_remaining.apply(idx);
            let jdx_goes = p_remaining.apply(idx + 1);
            if idx_goes > jdx_goes {
                let cur_swap = Permutation::transposition(p_remaining.len(), idx, idx + 1);
                first_layer.monoidal(
                    FrobeniusOperation::SymmetricBraiding(types_now[idx], types_now[idx + 1])
                        .into(),
                );
                in_place_permute(&mut types_now, &cur_swap);
                p_remaining = cur_swap * p_remaining;
            } else {
                first_layer.monoidal(FrobeniusOperation::Identity(types_now[idx]).into());
                first_layer.monoidal(FrobeniusOperation::Identity(types_now[idx + 1]).into());
            }
        }
        if p_remaining.len() % 2 == 1 {
            first_layer
                .monoidal(FrobeniusOperation::Identity(types_now[p_remaining.len() - 1]).into());
        }
        let mut second_layer: Self = FrobeniusOperation::Identity(types_now[0]).into();
        for idx in (1..p_remaining.len() - 1).step_by(2) {
            let idx_goes = p_remaining.apply(idx);
            let jdx_goes = p_remaining.apply(idx + 1);
            if idx_goes > jdx_goes {
                let cur_swap = Permutation::transposition(p_remaining.len(), idx, idx + 1);
                second_layer.monoidal(
                    FrobeniusOperation::SymmetricBraiding(types_now[idx], types_now[idx + 1])
                        .into(),
                );
                in_place_permute(&mut types_now, &cur_swap);
                p_remaining = cur_swap * p_remaining;
            } else {
                second_layer.monoidal(FrobeniusOperation::Identity(types_now[idx]).into());
                second_layer.monoidal(FrobeniusOperation::Identity(types_now[idx + 1]).into());
            }
        }
        if p_remaining.len() % 2 == 0 {
            second_layer
                .monoidal(FrobeniusOperation::Identity(types_now[p_remaining.len() - 1]).into());
        }
        first_layer.compose(second_layer).unwrap();
        let remaining = Self::from_permutation(p_remaining, &types_now, true);
        first_layer.compose(remaining).unwrap();
        assert_eq!(first_layer.domain(), types);
        let mut types_after_all_p = types.to_vec();
        in_place_permute(&mut types_after_all_p, &p.inv());
        assert_eq!(first_layer.codomain(), types_after_all_p);
        first_layer
    }
}

pub fn special_frobenius_morphism<Lambda: Eq + Copy + Debug, BlackBoxLabel: Eq + Copy>(
    m: usize,
    n: usize,
    wire_type: Lambda,
) -> FrobeniusMorphism<Lambda, BlackBoxLabel> {
    match (m, n) {
        (2, 1) => FrobeniusOperation::Multiplication(wire_type).into(),
        (1, 2) => FrobeniusOperation::Comultiplication(wire_type).into(),
        (1, 0) => FrobeniusOperation::Counit(wire_type).into(),
        (0, 1) => FrobeniusOperation::Unit(wire_type).into(),
        (1, 1) => FrobeniusOperation::Identity(wire_type).into(),
        _ => {
            if m < n {
                let mut x = special_frobenius_morphism(n, m, wire_type);
                x.hflip(&identity);
                x
            } else if n != 1 {
                let mut x = special_frobenius_morphism(m, 1, wire_type);
                let y = special_frobenius_morphism(1, n, wire_type);
                let _ = x.compose(y);
                x
            } else if m % 2 == 0 {
                let mut answer = special_frobenius_morphism(m / 2, 1, wire_type);
                answer.monoidal(answer.clone());
                let _ = answer.compose(FrobeniusOperation::Multiplication(wire_type).into());
                answer
            } else {
                let mut answer = special_frobenius_morphism(m - 1, 1, wire_type);
                answer.monoidal(FrobeniusOperation::Identity(wire_type).into());
                let _ = answer.compose(FrobeniusOperation::Multiplication(wire_type).into());
                answer
            }
        }
    }
}

#[allow(dead_code)]
pub fn from_decomposition<Lambda, BlackBoxLabel>(
    v: Decomposition,
    source_types: &[Lambda],
    target_types: &[Lambda],
) -> FrobeniusMorphism<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy + Debug,
    BlackBoxLabel: Eq + Copy,
{
    let (perm_part, surj_part, inj_part) = v.get_parts();
    let mut answer = FrobeniusMorphism::from_permutation(perm_part.clone(), source_types, true);

    let mut surj_part_frob = FrobeniusMorphism::<Lambda, BlackBoxLabel>::new();
    let mut after_perm_number = 0;
    for (_n, c) in surj_part.preimage_cardinalities().iter().enumerate() {
        let after_perm_types = &answer.codomain()[after_perm_number..after_perm_number + c];
        assert!(after_perm_types.iter().all(|l| *l == after_perm_types[0]));
        let cur_part = special_frobenius_morphism::<_, BlackBoxLabel>(*c, 1, after_perm_types[0]);
        surj_part_frob.monoidal(cur_part);
        after_perm_number += c;
    }

    let mut inj_part_frob = FrobeniusMorphism::<Lambda, BlackBoxLabel>::new();
    let mut target_number = 0;
    for (n, c) in inj_part.iden_unit_counts().iter().enumerate() {
        if n % 2 == 0 {
            let cur_iden_type = target_types[target_number..target_number + c].to_vec();
            inj_part_frob.monoidal(FrobeniusMorphism::identity(&cur_iden_type));
            target_number += c;
        } else {
            for idx in 0..*c {
                inj_part_frob
                    .monoidal(FrobeniusOperation::Unit(target_types[target_number + idx]).into());
            }
            target_number += c;
        }
    }

    assert!(
        answer.compose(surj_part_frob).is_ok(),
        "The provided source and target types did not line up for the given decomposed finite set map"
    );
    assert!(
        answer.compose(inj_part_frob).is_ok(),
        "The provided source and target types did not line up for the given decomposed finite set map"
    );
    answer
}

// TODO implement and test
pub trait Frobenius<Lambda: Eq + Copy + Debug, BlackBoxLabel: Eq + Copy>:
    SymmetricMonoidalMutatingMorphism<Lambda> + HasIdentity<Vec<Lambda>>
{
    fn interpret_unit(z: Lambda) -> Self;
    fn interpret_counit(z: Lambda) -> Self;
    fn interpret_multiplication(z: Lambda) -> Self;
    fn interpret_comultiplication(z: Lambda) -> Self;

    fn basic_interpret<F>(
        single_step: &FrobeniusOperation<Lambda, BlackBoxLabel>,
        black_box_interpreter: &F,
    ) -> Result<Self, String>
    where
        F: Fn(&BlackBoxLabel, &[Lambda], &[Lambda]) -> Result<Self, String>,
    {
        Ok(match single_step {
            FrobeniusOperation::Unit(z) => Self::interpret_unit(*z),
            FrobeniusOperation::Counit(z) => Self::interpret_counit(*z),
            FrobeniusOperation::Multiplication(z) => Self::interpret_multiplication(*z),
            FrobeniusOperation::Comultiplication(z) => Self::interpret_comultiplication(*z),
            FrobeniusOperation::Identity(z) => Self::identity(&vec![*z]),
            FrobeniusOperation::SymmetricBraiding(z1, z2) => {
                let transposition = Permutation::try_from(vec![0, 1]).unwrap();
                Self::from_permutation(transposition, &[*z1, *z2], true)
            }
            FrobeniusOperation::UnSpecifiedBox(bbl, z1, z2) => black_box_interpreter(bbl, z1, z2)?,
        })
    }

    fn interpret<F>(
        morphism: &FrobeniusMorphism<Lambda, BlackBoxLabel>,
        black_box_interpreter: &F,
    ) -> Result<Self, String>
    where
        F: Fn(&BlackBoxLabel, &[Lambda], &[Lambda]) -> Result<Self, String>,
    {
        let mut answer = Self::identity(&morphism.domain());
        for layer in &morphism.layers {
            if layer.blocks.is_empty() {
                return Err("???".to_string());
            }
            let first = &layer.blocks[0];
            let mut cur_layer = Self::basic_interpret(&first.op, black_box_interpreter)?;
            for block in &layer.blocks[1..] {
                cur_layer.monoidal(Self::basic_interpret(&block.op, black_box_interpreter)?);
            }
            answer.compose(cur_layer)?;
        }
        Ok(answer)
    }
}

impl<Lambda, BlackBoxLabel> Frobenius<Lambda, BlackBoxLabel>
    for FrobeniusMorphism<Lambda, BlackBoxLabel>
where
    Lambda: Eq + Copy + Debug,
    BlackBoxLabel: Eq + Copy,
{
    fn interpret_unit(z: Lambda) -> Self {
        FrobeniusOperation::Unit(z).into()
    }
    fn interpret_counit(z: Lambda) -> Self {
        FrobeniusOperation::Counit(z).into()
    }
    fn interpret_multiplication(z: Lambda) -> Self {
        FrobeniusOperation::Multiplication(z).into()
    }
    fn interpret_comultiplication(z: Lambda) -> Self {
        FrobeniusOperation::Comultiplication(z).into()
    }

    fn basic_interpret<F>(
        single_step: &FrobeniusOperation<Lambda, BlackBoxLabel>,
        _black_box_interpreter: &F,
    ) -> Result<Self, String>
    where
        F: Fn(&BlackBoxLabel, &[Lambda], &[Lambda]) -> Result<Self, String>,
    {
        Ok(single_step.clone().into())
    }

    fn interpret<F>(
        morphism: &FrobeniusMorphism<Lambda, BlackBoxLabel>,
        _black_box_interpreter: &F,
    ) -> Result<Self, String>
    where
        F: Fn(&BlackBoxLabel, &[Lambda], &[Lambda]) -> Result<Self, String>,
    {
        Ok(morphism.clone())
    }
}

mod test {

    #[test]
    fn rand_spiders() {
        use super::{special_frobenius_morphism, FrobeniusMorphism};
        use crate::category::ComposableMutating;
        use rand::distributions::Uniform;
        use rand::prelude::Distribution;
        let between = Uniform::from(0..5);
        let mut rng = rand::thread_rng();
        for _ in 0..10 {
            let m = between.sample(&mut rng);
            let n = between.sample(&mut rng);
            let rand_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(m, n, ());
            let exp_source_type: Vec<()> = (0..m).map(|_| ()).collect();
            let exp_target_type: Vec<()> = (0..n).map(|_| ()).collect();
            assert_eq!(exp_source_type, rand_spider.domain());
            assert_eq!(exp_target_type, rand_spider.codomain());
        }
        let between = Uniform::from(128..255);
        let mut rng = rand::thread_rng();
        for _ in 0..5 {
            let m = between.sample(&mut rng);
            let n = between.sample(&mut rng);
            let rand_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(m, n, ());
            let exp_source_type: Vec<()> = (0..m).map(|_| ()).collect();
            let exp_target_type: Vec<()> = (0..n).map(|_| ()).collect();
            assert_eq!(exp_source_type, rand_spider.domain());
            assert_eq!(exp_target_type, rand_spider.codomain());
            assert!(
                rand_spider.depth() <= 4 * 8,
                "Depth of {} to {} was {} instead of {}",
                m,
                n,
                rand_spider.depth(),
                4 * 8
            );
        }
    }

    #[test]
    fn basic_spiders() {
        use super::{special_frobenius_morphism, FrobeniusMorphism, FrobeniusOperation};
        let counit_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(1, 0, ());
        let exp_counit_spider: FrobeniusMorphism<_, _> = FrobeniusOperation::Counit(()).into();
        assert!(exp_counit_spider == counit_spider);
        assert_eq!(counit_spider.depth(), 1);

        let comul_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(1, 2, ());
        let exp_comul_spider: FrobeniusMorphism<_, _> =
            FrobeniusOperation::Comultiplication(()).into();
        assert!(exp_comul_spider == comul_spider);
        assert_eq!(comul_spider.depth(), 1);

        let mul_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(2, 1, ());
        let exp_mul_spider: FrobeniusMorphism<_, _> = FrobeniusOperation::Multiplication(()).into();
        assert!(exp_mul_spider == mul_spider);
        assert_eq!(mul_spider.depth(), 1);

        let unit_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(0, 1, ());
        let exp_unit_spider: FrobeniusMorphism<_, _> = FrobeniusOperation::Unit(()).into();
        assert!(exp_unit_spider == unit_spider);
        assert_eq!(unit_spider.depth(), 1);

        let id_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(1, 1, ());
        let exp_id_spider: FrobeniusMorphism<_, _> = FrobeniusOperation::Identity(()).into();
        assert!(exp_id_spider == id_spider);
        assert_eq!(id_spider.depth(), 1);
    }

    #[test]
    fn basic_typed_spiders() {
        use super::{special_frobenius_morphism, FrobeniusMorphism, FrobeniusOperation};
        let counit_spider: FrobeniusMorphism<bool, ()> = special_frobenius_morphism(1, 0, true);
        let exp_counit_spider: FrobeniusMorphism<_, _> = FrobeniusOperation::Counit(true).into();
        assert!(exp_counit_spider == counit_spider);

        let comul_spider: FrobeniusMorphism<bool, ()> = special_frobenius_morphism(1, 2, false);
        let exp_comul_spider: FrobeniusMorphism<_, _> =
            FrobeniusOperation::Comultiplication(false).into();
        assert!(exp_comul_spider == comul_spider);

        #[derive(PartialEq, Eq, Clone, Copy, Debug)]
        enum Color {
            Red,
            Green,
            Blue,
        }
        let mul_spider: FrobeniusMorphism<Color, ()> = special_frobenius_morphism(2, 1, Color::Red);
        let exp_mul_spider: FrobeniusMorphism<_, _> =
            FrobeniusOperation::Multiplication(Color::Red).into();
        assert!(exp_mul_spider == mul_spider);
        let exp_mul_spider: FrobeniusMorphism<_, _> =
            FrobeniusOperation::Multiplication(Color::Green).into();
        assert!(exp_mul_spider != mul_spider);

        let unit_spider: FrobeniusMorphism<Color, ()> =
            special_frobenius_morphism(0, 1, Color::Blue);
        let exp_unit_spider: FrobeniusMorphism<_, _> = FrobeniusOperation::Unit(Color::Blue).into();
        assert!(exp_unit_spider == unit_spider);

        let id_spider: FrobeniusMorphism<Color, ()> =
            special_frobenius_morphism(1, 1, Color::Green);
        let exp_id_spider: FrobeniusMorphism<_, _> =
            FrobeniusOperation::Identity(Color::Green).into();
        assert!(exp_id_spider == id_spider);
        let exp_id_spider: FrobeniusMorphism<_, _> =
            FrobeniusOperation::Identity(Color::Blue).into();
        assert!(exp_id_spider != id_spider);
    }

    #[test]
    fn permutation_automatic() {
        use super::{FrobeniusMorphism, FrobeniusOperation};
        use crate::category::ComposableMutating;
        use crate::symmetric_monoidal::SymmetricMonoidalMutatingMorphism;
        use crate::utils::{in_place_permute, rand_perm};
        use rand::distributions::Uniform;
        use rand::prelude::Distribution;
        let n_max = 10;
        let between = Uniform::<usize>::from(2..n_max);
        let mut rng = rand::thread_rng();
        let my_n = between.sample(&mut rng);
        let types_as_on_source = true;
        let domain_types = (0..my_n).map(|idx| idx + 100).collect::<Vec<usize>>();
        let p1 = rand_perm(my_n, my_n * 2);
        let frob_p1 = FrobeniusMorphism::<usize, ()>::from_permutation(
            p1.clone(),
            &domain_types,
            types_as_on_source,
        );
        let mut frob_prod = frob_p1.clone();
        assert_eq!(frob_prod.domain(), domain_types);
        let mut types_after_this_layer = domain_types.clone();
        in_place_permute(&mut types_after_this_layer, &p1.inv());
        assert_eq!(frob_prod.codomain(), types_after_this_layer);
        let p2 = rand_perm(my_n, my_n * 2);
        let frob_p2 = FrobeniusMorphism::from_permutation(
            p2.clone(),
            &frob_p1.codomain(),
            types_as_on_source,
        );
        frob_prod.compose(frob_p2).unwrap();
        in_place_permute(&mut types_after_this_layer, &p2.inv());
        assert_eq!(frob_prod.domain(), domain_types);
        assert_eq!(frob_prod.codomain(), types_after_this_layer);
        let types_as_on_source = false;
        let p3 = rand_perm(my_n, my_n * 2);
        let mut types_after_p3 = frob_prod.codomain().clone();
        in_place_permute(&mut types_after_p3, &p3.inv());
        let frob_p3 = FrobeniusMorphism::<usize, ()>::from_permutation(
            p3.clone(),
            &types_after_p3,
            types_as_on_source,
        );
        frob_prod.compose(frob_p3).unwrap();
        assert_eq!(frob_prod.domain(), domain_types);
        assert_eq!(frob_prod.codomain(), types_after_p3);
        let all_swaps = frob_prod.layers.iter().all(|layer| {
            layer.blocks.iter().all(|block| match block.op {
                FrobeniusOperation::SymmetricBraiding(_, _) => true,
                FrobeniusOperation::Identity(_) => true,
                _ => false,
            })
        });
        assert!(all_swaps);
    }

    #[test]
    fn decomposition_automatic() {
        use super::{from_decomposition, FrobeniusMorphism};
        use crate::finset::Decomposition;
        use rand::distributions::Uniform;
        use rand::prelude::Distribution;
        let in_max = 20;
        let out_max = 20;
        let mut rng = rand::thread_rng();
        let between = Uniform::<usize>::from(2..in_max);
        let my_in = between.sample(&mut rng);
        let between = Uniform::<usize>::from(2..out_max);
        let my_out = between.sample(&mut rng);
        let cur_test = (0..my_in)
            .map(|_| Uniform::<usize>::from(0..my_out).sample(&mut rng))
            .collect::<Vec<usize>>();
        let domain_types = (0..my_in)
            .map(|idx| cur_test[idx] + 100)
            .collect::<Vec<usize>>();
        let mut codomain_types = (0..my_out).map(|idx| idx + 40).collect::<Vec<usize>>();
        for (idx, idx_goes) in cur_test.iter().enumerate() {
            codomain_types[*idx_goes] = domain_types[idx];
        }
        let cur_res = Decomposition::try_from((cur_test.clone(), 0));
        if let Ok(cur_decomp) = cur_res {
            let _x: FrobeniusMorphism<_, ()> =
                from_decomposition(cur_decomp, &domain_types, &codomain_types);
        } else {
            assert!(false, "All maps of finite sets decompose");
        }
    }
}
