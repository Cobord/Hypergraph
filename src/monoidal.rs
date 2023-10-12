use std::marker::PhantomData;

use itertools::Itertools;

use crate::{
    category::CompositionError,
    frobenius_system::{Contains, InterpretError, InterpretableMorphism},
};

use {
    crate::category::{Composable, ComposableMutating, HasIdentity},
    std::fmt::Debug,
};

pub trait Monoidal {
    /*
    change the morphism self to the morphism (self \otimes other)
    */
    fn monoidal(&mut self, other: Self);
}

#[derive(PartialEq, Eq, Clone)]
pub struct GenericMonoidalMorphismLayer<BoxType, Lambda>
where
    Lambda: Eq + Copy,
    BoxType: Eq + Clone,
{
    /*
    a single layer for a black box filled morphism
    in a monoidal category whose objects
        are presented as tensor products of Lambda
    the black boxes are labelled with BoxType
    */
    pub blocks: Vec<BoxType>,
    pub left_type: Vec<Lambda>,
    pub right_type: Vec<Lambda>,
}

impl<Lambda, BoxType> Contains<BoxType> for GenericMonoidalMorphismLayer<BoxType, Lambda>
where
    Lambda: Eq + Copy,
    BoxType: Eq + Clone,
{
    fn contained_labels(&self) -> Vec<BoxType> {
        self.blocks.clone()
    }
}

impl<BoxType, Lambda> GenericMonoidalMorphismLayer<BoxType, Lambda>
where
    Lambda: Eq + Copy,
    BoxType: Eq + Clone,
{
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self {
            blocks: vec![],
            left_type: vec![],
            right_type: vec![],
        }
    }
}

impl<BoxType, Lambda> HasIdentity<Vec<Lambda>> for GenericMonoidalMorphismLayer<BoxType, Lambda>
where
    Lambda: Eq + Copy,
    BoxType: Eq + Clone + HasIdentity<Lambda>,
{
    fn identity(on_type: &Vec<Lambda>) -> Self {
        let mut answer = Self::new();
        for cur_type in on_type {
            let op = BoxType::identity(cur_type);
            answer.blocks.push(op);
            answer.left_type.push(*cur_type);
            answer.right_type.push(*cur_type);
        }
        answer
    }
}

impl<BoxType, Lambda> Monoidal for GenericMonoidalMorphismLayer<BoxType, Lambda>
where
    Lambda: Eq + Copy,
    BoxType: Eq + Clone,
{
    fn monoidal(&mut self, other: Self) {
        self.blocks.extend(other.blocks);
        self.left_type.extend(other.left_type);
        self.right_type.extend(other.right_type);
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy,
    BoxType: Eq + Clone,
{
    /*
    a black box filled morphism
    in a monoidal category whose objects
        are presented as tensor products of Lambda
    the black boxes are labelled with BoxType
    when given a function from BoxType to the
        actual type for the morphisms in the desired category
        one can interpret this as the aforementioned type
        by building up with composition and monoidal
    */
    layers: Vec<GenericMonoidalMorphismLayer<BoxType, Lambda>>,
}

impl<Lambda, BoxType> Contains<BoxType> for GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy,
    BoxType: Eq + Clone,
{
    fn contained_labels(&self) -> Vec<BoxType> {
        self.layers
            .iter()
            .flat_map(|layer| layer.contained_labels())
            .collect_vec()
    }
}

impl<Lambda, BoxType> GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy,
    BoxType: Eq + Clone,
{
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self { layers: vec![] }
    }

    #[allow(dead_code)]
    pub fn depth(&self) -> usize {
        self.layers.len()
    }

    #[allow(dead_code)]
    fn append_layer(
        &mut self,
        next_layer: GenericMonoidalMorphismLayer<BoxType, Lambda>,
    ) -> Result<(), CompositionError> {
        let last_so_far = self.layers.pop();
        match last_so_far {
            None => {
                self.layers.push(next_layer);
            }
            Some(v) => {
                if v.right_type != next_layer.left_type {
                    return Err("type mismatch in morphims composition".into());
                }
                self.layers.push(v);
                self.layers.push(next_layer);
            }
        }
        Ok(())
    }

    pub fn extract_layers(self) -> Vec<GenericMonoidalMorphismLayer<BoxType, Lambda>> {
        self.layers
    }
}

impl<Lambda, BoxType> HasIdentity<Vec<Lambda>> for GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy,
    BoxType: Eq + Clone + HasIdentity<Lambda>,
{
    fn identity(on_this: &Vec<Lambda>) -> Self {
        Self {
            layers: vec![<_>::identity(on_this)],
        }
    }
}

impl<Lambda, BoxType> Monoidal for GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy + Debug,
    BoxType: Eq + Clone + HasIdentity<Lambda>,
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
            let mut new_layer = GenericMonoidalMorphismLayer::identity(&last_self_type);
            new_layer.monoidal(other.layers[n].clone());
            let _ = self.append_layer(new_layer);
        }
    }
}

fn layers_composable<Lambda, BoxType>(
    l: &[GenericMonoidalMorphismLayer<BoxType, Lambda>],
    r: &[GenericMonoidalMorphismLayer<BoxType, Lambda>],
) -> Result<(), CompositionError>
where
    Lambda: Eq + Copy + Debug,
    BoxType: Eq + Clone,
{
    if l.is_empty() || r.is_empty() {
        if l.is_empty() && r.is_empty() {
            return Ok(());
        } else if l.is_empty() {
            let other_interface = &r[0].left_type;
            if other_interface.is_empty() {
                return Ok(());
            } else {
                return Err("Mismatch in cardinalities of common interface".into());
            }
        } else {
            let self_interface = &l.last().unwrap().right_type;
            if self_interface.is_empty() {
                return Ok(());
            } else {
                return Err("Mismatch in cardinalities of common interface".into());
            }
        }
    }
    let self_interface = &l.last().unwrap().right_type;
    let other_interface = &r[0].left_type;
    if self_interface.len() != other_interface.len() {
        Err("Mismatch in cardinalities of common interface".into())
    } else if self_interface != other_interface {
        for idx in 0..self_interface.len() {
            let w1 = self_interface[idx];
            let w2 = other_interface[idx];
            if w1 != w2 {
                return Err(format!(
                    "Mismatch in labels of common interface. At some index there was {:?} vs {:?}",
                    w1, w2
                )
                .into());
            }
        }
        Err("Mismatch in labels of common interface at some unknown index.".into())
    } else {
        Ok(())
    }
}

impl<Lambda, BoxType> ComposableMutating<Vec<Lambda>> for GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy + Debug,
    BoxType: Eq + Clone,
{
    fn composable(&self, other: &Self) -> Result<(), CompositionError> {
        layers_composable(&self.layers, &other.layers)
    }

    fn compose(&mut self, other: Self) -> Result<(), CompositionError> {
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

pub trait MonoidalMorphism<T: Eq>: Monoidal + Composable<T> {}
pub trait MonoidalMutatingMorphism<T: Eq>: Monoidal + ComposableMutating<T> {}

impl<Lambda, BoxType> MonoidalMutatingMorphism<Vec<Lambda>>
    for GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy + Debug,
    BoxType: Eq + HasIdentity<Lambda> + Clone,
{
    /*
    the most obvious implementation of MonoidalMutatingMorphism is GenericMonoidalMorphism itself
    use all the structure of monoidal, compose, identity provided by concatenating blocks and layers appropriately
    */
}

struct InterpretableNoMut<T, Lambda>
where
    Lambda: Eq,
    T: Monoidal + Composable<Vec<Lambda>> + HasIdentity<Vec<Lambda>>,
{
    me: T,
    dummy: PhantomData<Lambda>,
}

impl<T, Lambda> InterpretableNoMut<T, Lambda>
where
    Lambda: Eq,
    T: Monoidal + Composable<Vec<Lambda>> + HasIdentity<Vec<Lambda>>,
{
    #[allow(dead_code)]
    fn change_black_boxer<F1, BoxType>(
        f1: F1,
    ) -> impl Fn(&BoxType, &[Lambda], &[Lambda]) -> Result<Self, InterpretError>
    where
        F1: Fn(&BoxType) -> Result<T, InterpretError>,
    {
        move |bb, _, _| f1(bb).map(Self::from)
    }
}

impl<T, Lambda> From<T> for InterpretableNoMut<T, Lambda>
where
    Lambda: Eq,
    T: Monoidal + Composable<Vec<Lambda>> + HasIdentity<Vec<Lambda>>,
{
    fn from(me: T) -> Self {
        Self {
            me,
            dummy: PhantomData,
        }
    }
}

struct InterpretableMut<T, Lambda>
where
    Lambda: Eq,
    T: Monoidal + ComposableMutating<Vec<Lambda>> + HasIdentity<Vec<Lambda>>,
{
    me: T,
    dummy: PhantomData<Lambda>,
}

impl<T, Lambda> InterpretableMut<T, Lambda>
where
    Lambda: Eq,
    T: Monoidal + ComposableMutating<Vec<Lambda>> + HasIdentity<Vec<Lambda>>,
{
    #[allow(dead_code)]
    fn change_black_boxer<F1, BoxType>(
        f1: F1,
    ) -> impl Fn(&BoxType, &[Lambda], &[Lambda]) -> Result<Self, InterpretError>
    where
        F1: Fn(&BoxType) -> Result<T, InterpretError>,
    {
        move |bb, _, _| f1(bb).map(Self::from)
    }
}

impl<T, Lambda> From<T> for InterpretableMut<T, Lambda>
where
    Lambda: Eq,
    T: Monoidal + ComposableMutating<Vec<Lambda>> + HasIdentity<Vec<Lambda>>,
{
    fn from(me: T) -> Self {
        Self {
            me,
            dummy: PhantomData,
        }
    }
}

impl<Lambda, BoxType, T>
    InterpretableMorphism<GenericMonoidalMorphism<BoxType, Lambda>, Lambda, BoxType>
    for InterpretableMut<T, Lambda>
where
    Lambda: Eq + Copy + Debug,
    BoxType: Eq + Clone,
    T: Monoidal + ComposableMutating<Vec<Lambda>> + HasIdentity<Vec<Lambda>>,
{
    /*
    given a function from BoxType to the
        actual type (Self) for the morphisms in the desired category
        one can interpret a GenericaMonoidalMorphism as a Self
        by building up with composition and monoidal
    */
    fn interpret<F>(
        morphism: &GenericMonoidalMorphism<BoxType, Lambda>,
        black_box_interpreter: F,
    ) -> Result<Self, InterpretError>
    where
        F: Fn(&BoxType, &[Lambda], &[Lambda]) -> Result<Self, InterpretError>,
    {
        let mut answer = T::identity(&morphism.domain());
        for layer in &morphism.layers {
            let Some(first) = &layer.blocks.first() else {
                return Err("somehow an empty layer in a generica monoidal morphism???".into());
            };
            let mut cur_layer = black_box_interpreter(first, &[], &[]).map(|z| z.me)?;
            for block in &layer.blocks[1..] {
                cur_layer.monoidal(black_box_interpreter(block, &[], &[]).map(|z| z.me)?);
            }
            answer.compose(cur_layer).map_err(|e| format!("{:?}", e))?;
        }
        Ok(Self::from(answer))
    }
}

impl<Lambda, BoxType, T>
    InterpretableMorphism<GenericMonoidalMorphism<BoxType, Lambda>, Lambda, BoxType>
    for InterpretableNoMut<T, Lambda>
where
    Lambda: Eq + Copy + Debug,
    BoxType: Eq + Clone,
    T: Monoidal + Composable<Vec<Lambda>> + HasIdentity<Vec<Lambda>>,
{
    /*
    given a function from BoxType to the
        actual type (Self) for the morphisms in the desired category
        one can interpret a GenericaMonoidalMorphism as a Self
        by building up with composition and monoidal
    only different from above because of the distinction between compositions
        that are done by modifying self to the composition self;other
        or that return a new self;other
    */
    fn interpret<F>(
        morphism: &GenericMonoidalMorphism<BoxType, Lambda>,
        black_box_interpreter: F,
    ) -> Result<Self, InterpretError>
    where
        F: Fn(&BoxType, &[Lambda], &[Lambda]) -> Result<Self, InterpretError>,
    {
        let mut answer = T::identity(&morphism.domain());
        for layer in &morphism.layers {
            let Some(first) = &layer.blocks.first() else {
                return Err("somehow an empty layer in a generica monoidal morphism???".into());
            };
            let mut cur_layer = black_box_interpreter(first, &[], &[]).map(|z| z.me)?;
            for block in &layer.blocks[1..] {
                cur_layer.monoidal(black_box_interpreter(block, &[], &[]).map(|z| z.me)?);
            }
            answer = answer.compose(&cur_layer).map_err(|e| format!("{:?}", e))?;
        }
        Ok(Self::from(answer))
    }
}
