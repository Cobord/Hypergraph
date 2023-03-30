use permutations::Permutation;
use std::convert::identity;
use std::fmt::Debug;

use crate::category::{ComposableMutating, HasIdentity};
use crate::monoidal::{Monoidal, MonoidalMutatingMorphism};
use crate::symmetric_monoidal::SymmetricMonoidalMutatingMorphism;

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
            Self::Multiplication(_) => 2,
            Self::Comultiplication(_) => 1,
            Self::Counit(_) => 1,
            Self::Identity(_) => 1,
            Self::SymmetricBraiding(_, _) => 2,
            Self::UnSpecifiedBox(_, srcs, _) => srcs.len(),
        }
    }

    fn target_size(&self) -> usize {
        match self {
            Self::Unit(_) => 1,
            Self::Multiplication(_) => 1,
            Self::Comultiplication(_) => 2,
            Self::Counit(_) => 0,
            Self::Identity(_) => 1,
            Self::SymmetricBraiding(_, _) => 2,
            Self::UnSpecifiedBox(_, _, tgts) => tgts.len(),
        }
    }

    fn source_types(&self) -> Vec<Lambda> {
        match self {
            Self::Unit(_) => vec![],
            Self::Multiplication(z) => vec![*z, *z],
            Self::Comultiplication(z) => vec![*z],
            Self::Counit(z) => vec![*z],
            Self::Identity(z) => vec![*z],
            Self::SymmetricBraiding(z, w) => vec![*z, *w],
            Self::UnSpecifiedBox(_, srcs, _) => srcs.clone(),
        }
    }

    fn target_types(&self) -> Vec<Lambda> {
        match self {
            Self::Unit(z) => vec![*z],
            Self::Multiplication(z) => vec![*z],
            Self::Comultiplication(z) => vec![*z, *z],
            Self::Counit(_) => vec![],
            Self::Identity(z) => vec![*z],
            Self::SymmetricBraiding(z, w) => vec![*w, *z],
            Self::UnSpecifiedBox(_, _, tgts) => tgts.clone(),
        }
    }

    fn hflip<F>(&mut self, black_box_changer: F)
    where
        F: Fn(BlackBoxLabel) -> BlackBoxLabel,
    {
        let new_self = match self {
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
        *self = new_self;
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
        let my_source_size = self.source_size();
        (0..my_source_size)
            .map(|z| z + self.source_side_placement)
            .collect()
    }

    fn target_size(&self) -> usize {
        self.op.target_size()
    }

    #[allow(dead_code)]
    fn target_idces(&self) -> Vec<usize> {
        let my_target_size = self.target_size();
        (0..my_target_size)
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
        for block_num in 0..self.blocks.len() {
            self.blocks[block_num].hflip(black_box_changer);
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
        let my_op = FrobeniusBlock::<Lambda, BlackBoxLabel>::new(
            op,
            source_side_placement,
            target_side_placement,
        );
        self.blocks.push(my_op);
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
            let op = FrobeniusOperation::Identity(*cur_type);
            answer.append_block(op);
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

    pub fn single_op(op: FrobeniusOperation<Lambda, BlackBoxLabel>) -> Self {
        let mut answer_layer = FrobeniusLayer::new();
        answer_layer.append_block(op);
        let mut answer = FrobeniusMorphism::new();
        let _ = answer.append_layer(answer_layer);
        answer
    }

    fn append_layer(
        &mut self,
        next_layer: FrobeniusLayer<Lambda, BlackBoxLabel>,
    ) -> Result<(), String> {
        let last_so_far = self.layers.pop();
        match last_so_far {
            None => {
                self.layers.push(next_layer);
            }
            Some(v) => {
                if v.right_type != next_layer.left_type {
                    return Err("type mismatch in frobenius morphims composition".to_string());
                }
                self.layers.push(v);
                self.layers.push(next_layer);
            }
        }
        Ok(())
    }

    fn hflip<F>(&mut self, black_box_changer: &F)
    where
        F: Fn(BlackBoxLabel) -> BlackBoxLabel,
    {
        for layer_num in 0..self.layers.len() {
            self.layers[layer_num].hflip(black_box_changer);
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
        let empty_layer = FrobeniusLayer::identity(on_this);
        Self {
            layers: vec![empty_layer],
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
                let empty_layer = FrobeniusLayer::identity(&last_other_type);
                cur_self_layer.monoidal(empty_layer);
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
                let self_interface = &self.layers[self.layers.len() - 1].right_type;
                if self_interface.is_empty() {
                    return Ok(());
                } else {
                    return Err("Mismatch in cardinalities of common interface".to_string());
                }
            }
        }
        let self_interface = &self.layers[self.layers.len() - 1].right_type;
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
        if self.layers.is_empty() {
            vec![]
        } else {
            self.layers[0].left_type.clone()
        }
    }

    fn codomain(&self) -> Vec<Lambda> {
        if self.layers.is_empty() {
            vec![]
        } else {
            self.layers[self.layers.len() - 1].right_type.clone()
        }
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
        _p: permutations::Permutation,
        _types: &[Lambda],
        _types_as_on_domain: bool,
    ) -> Self {
        todo!()
    }
}

pub fn special_frobenius_morphism<Lambda: Eq + Copy + Debug, BlackBoxLabel: Eq + Copy>(
    m: usize,
    n: usize,
    wire_type: Lambda,
) -> FrobeniusMorphism<Lambda, BlackBoxLabel> {
    match (m, n) {
        (2, 1) => FrobeniusMorphism::single_op(FrobeniusOperation::Multiplication(wire_type)),
        (1, 2) => FrobeniusMorphism::single_op(FrobeniusOperation::Comultiplication(wire_type)),
        (1, 0) => FrobeniusMorphism::single_op(FrobeniusOperation::Counit(wire_type)),
        (0, 1) => FrobeniusMorphism::single_op(FrobeniusOperation::Unit(wire_type)),
        (1, 1) => FrobeniusMorphism::single_op(FrobeniusOperation::Identity(wire_type)),
        _ => {
            if m < n {
                let mut x = special_frobenius_morphism(n, m, wire_type);
                x.hflip(&|z| z);
                x
            } else if n != 1 {
                let mut x = special_frobenius_morphism(m, 1, wire_type);
                let y = special_frobenius_morphism(1, n, wire_type);
                let _ = x.compose(y);
                x
            } else if m % 2 == 0 {
                let mut answer = special_frobenius_morphism(m / 2, 1, wire_type);
                answer.monoidal(answer.clone());
                let _ = answer.compose(FrobeniusMorphism::single_op(
                    FrobeniusOperation::Multiplication(wire_type),
                ));
                answer
            } else {
                let mut answer = special_frobenius_morphism(m - 1, 1, wire_type);
                answer.monoidal(FrobeniusMorphism::single_op(FrobeniusOperation::Identity(
                    wire_type,
                )));
                let _ = answer.compose(FrobeniusMorphism::single_op(
                    FrobeniusOperation::Multiplication(wire_type),
                ));
                answer
            }
        }
    }
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
        let answer = match single_step {
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
        };
        Ok(answer)
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
            let _ = answer.compose(cur_layer)?;
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
        Self::single_op(FrobeniusOperation::Unit(z))
    }
    fn interpret_counit(z: Lambda) -> Self {
        Self::single_op(FrobeniusOperation::Counit(z))
    }
    fn interpret_multiplication(z: Lambda) -> Self {
        Self::single_op(FrobeniusOperation::Multiplication(z))
    }
    fn interpret_comultiplication(z: Lambda) -> Self {
        Self::single_op(FrobeniusOperation::Comultiplication(z))
    }

    fn basic_interpret<F>(
        single_step: &FrobeniusOperation<Lambda, BlackBoxLabel>,
        _black_box_interpreter: &F,
    ) -> Result<Self, String>
    where
        F: Fn(&BlackBoxLabel, &[Lambda], &[Lambda]) -> Result<Self, String>,
    {
        Ok(Self::single_op(single_step.clone()))
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
    #[allow(unused_imports)]
    use crate::category::ComposableMutating;

    #[test]
    fn rand_spiders() {
        use super::{special_frobenius_morphism, FrobeniusMorphism};
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
        let exp_counit_spider = FrobeniusMorphism::single_op(FrobeniusOperation::Counit(()));
        assert!(exp_counit_spider == counit_spider);
        assert_eq!(counit_spider.depth(), 1);

        let comul_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(1, 2, ());
        let exp_comul_spider =
            FrobeniusMorphism::single_op(FrobeniusOperation::Comultiplication(()));
        assert!(exp_comul_spider == comul_spider);
        assert_eq!(comul_spider.depth(), 1);

        let mul_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(2, 1, ());
        let exp_mul_spider = FrobeniusMorphism::single_op(FrobeniusOperation::Multiplication(()));
        assert!(exp_mul_spider == mul_spider);
        assert_eq!(mul_spider.depth(), 1);

        let unit_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(0, 1, ());
        let exp_unit_spider = FrobeniusMorphism::single_op(FrobeniusOperation::Unit(()));
        assert!(exp_unit_spider == unit_spider);
        assert_eq!(unit_spider.depth(), 1);

        let id_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(1, 1, ());
        let exp_id_spider = FrobeniusMorphism::single_op(FrobeniusOperation::Identity(()));
        assert!(exp_id_spider == id_spider);
        assert_eq!(id_spider.depth(), 1);
    }

    #[test]
    fn basic_typed_spiders() {
        use super::{special_frobenius_morphism, FrobeniusMorphism, FrobeniusOperation};
        let counit_spider: FrobeniusMorphism<bool, ()> = special_frobenius_morphism(1, 0, true);
        let exp_counit_spider = FrobeniusMorphism::single_op(FrobeniusOperation::Counit(true));
        assert!(exp_counit_spider == counit_spider);

        let comul_spider: FrobeniusMorphism<bool, ()> = special_frobenius_morphism(1, 2, false);
        let exp_comul_spider =
            FrobeniusMorphism::single_op(FrobeniusOperation::Comultiplication(false));
        assert!(exp_comul_spider == comul_spider);

        #[derive(PartialEq, Eq, Clone, Copy, Debug)]
        enum COLOR {
            RED,
            GREEN,
            BLUE,
        }
        let mul_spider: FrobeniusMorphism<COLOR, ()> = special_frobenius_morphism(2, 1, COLOR::RED);
        let exp_mul_spider =
            FrobeniusMorphism::single_op(FrobeniusOperation::Multiplication(COLOR::RED));
        assert!(exp_mul_spider == mul_spider);
        let exp_mul_spider =
            FrobeniusMorphism::single_op(FrobeniusOperation::Multiplication(COLOR::GREEN));
        assert!(exp_mul_spider != mul_spider);

        let unit_spider: FrobeniusMorphism<COLOR, ()> =
            special_frobenius_morphism(0, 1, COLOR::BLUE);
        let exp_unit_spider = FrobeniusMorphism::single_op(FrobeniusOperation::Unit(COLOR::BLUE));
        assert!(exp_unit_spider == unit_spider);

        let id_spider: FrobeniusMorphism<COLOR, ()> =
            special_frobenius_morphism(1, 1, COLOR::GREEN);
        let exp_id_spider =
            FrobeniusMorphism::single_op(FrobeniusOperation::Identity(COLOR::GREEN));
        assert!(exp_id_spider == id_spider);
        let exp_id_spider = FrobeniusMorphism::single_op(FrobeniusOperation::Identity(COLOR::BLUE));
        assert!(exp_id_spider != id_spider);
    }
}
