use crate::category::{Composable, ComposableMutating, HasIdentity};
use std::fmt::Debug;

pub trait Monoidal {
    fn monoidal(&mut self, other: Self);
}

#[derive(PartialEq, Eq, Clone)]
pub struct GenericMonoidalMorphismLayer<BoxType, Lambda: Eq + Copy> {
    pub blocks: Vec<BoxType>,
    pub left_type: Vec<Lambda>,
    pub right_type: Vec<Lambda>,
}

impl<BoxType, Lambda> GenericMonoidalMorphismLayer<BoxType, Lambda>
where
    Lambda: Eq + Copy,
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
    BoxType: HasIdentity<Lambda>,
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
{
    fn monoidal(&mut self, other: Self) {
        self.blocks.extend(other.blocks);
        self.left_type.extend(other.left_type);
        self.right_type.extend(other.right_type);
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct GenericMonoidalMorphism<BoxType, Lambda: Eq + Copy> {
    layers: Vec<GenericMonoidalMorphismLayer<BoxType, Lambda>>,
}

impl<Lambda, BoxType> GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy,
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
    ) -> Result<(), String> {
        let last_so_far = self.layers.pop();
        match last_so_far {
            None => {
                self.layers.push(next_layer);
            }
            Some(v) => {
                if v.right_type != next_layer.left_type {
                    return Err("type mismatch in morphims composition".to_string());
                }
                self.layers.push(v);
                self.layers.push(next_layer);
            }
        }
        Ok(())
    }
}

impl<Lambda, BoxType> HasIdentity<Vec<Lambda>> for GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy,
    BoxType: HasIdentity<Lambda>,
{
    #[allow(dead_code)]
    fn identity(on_this: &Vec<Lambda>) -> Self {
        let empty_layer = GenericMonoidalMorphismLayer::<BoxType, Lambda>::identity(on_this);
        Self {
            layers: vec![empty_layer],
        }
    }
}

impl<Lambda, BoxType> Monoidal for GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy + Debug,
    BoxType: Clone + HasIdentity<Lambda>,
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
                let empty_layer =
                    GenericMonoidalMorphismLayer::<BoxType, Lambda>::identity(&last_other_type);
                cur_self_layer.monoidal(empty_layer);
            }
        }
        for n in self_len..others_len {
            let mut new_layer =
                GenericMonoidalMorphismLayer::<BoxType, Lambda>::identity(&last_self_type);
            new_layer.monoidal(other.layers[n].clone());
            let _ = self.append_layer(new_layer);
        }
    }
}

fn layers_composable<Lambda: Eq + Copy + Debug, BoxType>(
    l: &[GenericMonoidalMorphismLayer<BoxType, Lambda>],
    r: &[GenericMonoidalMorphismLayer<BoxType, Lambda>],
) -> Result<(), String> {
    if l.is_empty() || r.is_empty() {
        if l.is_empty() && r.is_empty() {
            return Ok(());
        } else if l.is_empty() {
            let other_interface = &r[0].left_type;
            if other_interface.is_empty() {
                return Ok(());
            } else {
                return Err("Mismatch in cardinalities of common interface".to_string());
            }
        } else {
            let self_interface = &l.last().unwrap().right_type;
            if self_interface.is_empty() {
                return Ok(());
            } else {
                return Err("Mismatch in cardinalities of common interface".to_string());
            }
        }
    }
    let self_interface = &l.last().unwrap().right_type;
    let other_interface = &r[0].left_type;
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

impl<Lambda, BoxType> ComposableMutating<Vec<Lambda>> for GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy + Debug,
{
    fn composable(&self, other: &Self) -> Result<(), String> {
        layers_composable(&self.layers, &other.layers)
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

pub trait MonoidalMorphism<T: Eq>: Monoidal + Composable<T> {}
pub trait MonoidalMutatingMorphism<T: Eq>: Monoidal + ComposableMutating<T> {}

pub trait GenericMonoidalInterpretableMut<Lambda: Eq + Copy + Debug>:
    Monoidal + ComposableMutating<Vec<Lambda>> + HasIdentity<Vec<Lambda>>
{
    fn interpret<F, BoxType>(
        morphism: &GenericMonoidalMorphism<BoxType, Lambda>,
        black_box_interpreter: &F,
    ) -> Result<Self, String>
    where
        F: Fn(&BoxType) -> Result<Self, String>,
    {
        let mut answer = Self::identity(&morphism.domain());
        for layer in &morphism.layers {
            if layer.blocks.is_empty() {
                return Err("???".to_string());
            }
            let first = &layer.blocks[0];
            let mut cur_layer = black_box_interpreter(first)?;
            for block in &layer.blocks[1..] {
                cur_layer.monoidal(black_box_interpreter(block)?);
            }
            answer.compose(cur_layer)?;
        }
        Ok(answer)
    }
}
pub trait GenericMonoidalInterpretable<Lambda: Eq + Copy + Debug>:
    Monoidal + Composable<Vec<Lambda>> + HasIdentity<Vec<Lambda>>
{
    fn interpret<F, BoxType>(
        morphism: &GenericMonoidalMorphism<BoxType, Lambda>,
        black_box_interpreter: &F,
    ) -> Result<Self, String>
    where
        F: Fn(&BoxType) -> Result<Self, String>,
    {
        let mut answer = Self::identity(&morphism.domain());
        for layer in &morphism.layers {
            if layer.blocks.is_empty() {
                return Err("???".to_string());
            }
            let first = &layer.blocks[0];
            let mut cur_layer = black_box_interpreter(first)?;
            for block in &layer.blocks[1..] {
                cur_layer.monoidal(black_box_interpreter(block)?);
            }
            answer = answer.compose(&cur_layer)?;
        }
        Ok(answer)
    }
}

impl<Lambda, BoxType> MonoidalMutatingMorphism<Vec<Lambda>>
    for GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy + Debug,
    BoxType: HasIdentity<Lambda> + Clone,
{
}

impl<Lambda, BoxType> GenericMonoidalInterpretableMut<Lambda>
    for GenericMonoidalMorphism<BoxType, Lambda>
where
    Lambda: Eq + Copy + Debug,
    BoxType: HasIdentity<Lambda> + Clone,
{
}
