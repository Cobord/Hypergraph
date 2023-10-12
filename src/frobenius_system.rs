use {
    petgraph::{algo::toposort, prelude::DiGraph},
    std::{collections::HashMap, marker::PhantomData},
};

pub trait Contains<BlackBoxLabel> {
    fn contained_labels(&self) -> Vec<BlackBoxLabel>;
}

#[derive(Clone, Debug)]
pub enum InterpretError {
    InterpretError(String),
}

impl From<String> for InterpretError {
    fn from(value: String) -> Self {
        Self::InterpretError(value)
    }
}

impl From<&str> for InterpretError {
    fn from(value: &str) -> Self {
        Self::InterpretError(value.to_string())
    }
}

pub trait InterpretableMorphism<GeneralVersion, Lambda, BlackBoxLabel>: Sized {
    fn interpret<F>(gen: &GeneralVersion, black_box_interpreter: F) -> Result<Self, InterpretError>
    where
        F: Fn(&BlackBoxLabel, &[Lambda], &[Lambda]) -> Result<Self, InterpretError>;
}

#[allow(dead_code)]
struct MorphismSystem<BlackBoxLabel, Lambda, GeneralBlackBoxed, T>
where
    BlackBoxLabel: std::hash::Hash + Eq,
    T: InterpretableMorphism<GeneralBlackBoxed, Lambda, BlackBoxLabel>,
    GeneralBlackBoxed: Contains<BlackBoxLabel>,
{
    composite_pieces: HashMap<BlackBoxLabel, GeneralBlackBoxed>,
    simple_pieces: HashMap<BlackBoxLabel, T>,
    main: BlackBoxLabel,
    dag: DiGraph<BlackBoxLabel, ()>,
    dummy: PhantomData<Lambda>,
}

impl<GeneralBlackBoxed, BlackBoxLabel, Lambda, T>
    MorphismSystem<BlackBoxLabel, Lambda, GeneralBlackBoxed, T>
where
    BlackBoxLabel: std::hash::Hash + Eq + Clone + std::fmt::Debug,
    Lambda: Eq + std::fmt::Debug + Copy,
    T: InterpretableMorphism<GeneralBlackBoxed, Lambda, BlackBoxLabel> + Clone,
    GeneralBlackBoxed: Contains<BlackBoxLabel>,
{
    #[allow(dead_code)]
    pub fn new(_main_name: BlackBoxLabel) -> Self {
        todo!("new system")
    }

    #[allow(dead_code)]
    pub fn add_definition_composite(
        &mut self,
        _new_name: BlackBoxLabel,
        _new_def: GeneralBlackBoxed,
    ) {
        todo!("add a definition for a black boxed morphism with black boxes to be filled with other definitions")
    }

    #[allow(dead_code)]
    pub fn add_definition_simple(&mut self, _new_name: BlackBoxLabel, _new_def: T) {
        todo!("add a definition for a black boxed morphism that is directly a T")
    }

    #[allow(dead_code)]
    pub fn set_main(&mut self, main_name: BlackBoxLabel) {
        self.main = main_name;
    }

    #[allow(dead_code)]
    fn interpret_nomut(
        &self,
        interpret_target: Option<BlackBoxLabel>,
    ) -> Result<T, InterpretError> {
        let which_interpreting = interpret_target.unwrap_or(self.main.clone());
        if let Some(simple_answer) = self.simple_pieces.get(&which_interpreting) {
            return Ok(simple_answer.clone());
        }
        let complicated_answer = self.composite_pieces.get(&which_interpreting);
        if let Some(complicated_answer_2) = complicated_answer {
            let black_box_interpreter = |bb: &BlackBoxLabel, _src: &[Lambda], _tgt: &[Lambda]| {
                let simple_answer = self
                    .simple_pieces
                    .get(bb)
                    .ok_or(format!("No filling for {:?}", bb.clone()).into())
                    .map(|z| z.clone());
                if simple_answer.is_err() {
                    self.interpret_nomut(Some(bb.clone()))
                } else {
                    simple_answer
                }
            };
            T::interpret(complicated_answer_2, black_box_interpreter).map_err(
                |internal_explanation| {
                    format!(
                        "When doing {:?}\n{:?}",
                        which_interpreting, internal_explanation
                    )
                    .into()
                },
            )
        } else {
            Err(format!("No {:?} found", which_interpreting).into())
        }
    }

    #[allow(dead_code)]
    pub fn fill_black_boxes(
        &mut self,
        interpret_target: Option<BlackBoxLabel>,
    ) -> Result<T, InterpretError> {
        let which_interpreting = interpret_target.unwrap_or(self.main.clone());
        if let Some(simple_answer) = self.simple_pieces.get(&which_interpreting) {
            return Ok(simple_answer.clone());
        }
        let resolution_order = toposort(&self.dag, None);
        if let Ok(ordered) = resolution_order {
            for cur_node in ordered {
                let node_name = self.dag.node_weight(cur_node);
                if let Some(my_bb) = node_name {
                    let cur_answer = self.interpret_nomut(Some(my_bb.clone()));
                    if let Ok(real_cur_answer) = cur_answer.clone() {
                        self.simple_pieces.insert(my_bb.clone(), real_cur_answer);
                        let _ = self.composite_pieces.remove(my_bb);
                    }
                    if *my_bb == which_interpreting {
                        return cur_answer;
                    }
                } else {
                    return Err(
                        format!("Node {:?} not found after topological sort", cur_node).into(),
                    );
                }
            }
            Err(format!("Through all but never found {:?}", which_interpreting).into())
        } else {
            Err("Not acyclic dependencies".into())
        }
    }
}
