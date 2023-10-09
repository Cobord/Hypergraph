use {
    crate::frobenius::{Frobenius,FrobeniusMorphism},
    either::Either,
    petgraph::{algo::toposort, prelude::DiGraph},
    std::collections::HashMap,
};

#[allow(dead_code)]
struct FrobeniusSystem<BlackBoxLabel, Lambda, T>
where
    BlackBoxLabel: std::hash::Hash + Eq + Copy,
    Lambda: Eq + Copy + std::fmt::Debug,
    T: Frobenius<Lambda, BlackBoxLabel>,
{
    composite_pieces: HashMap<BlackBoxLabel, FrobeniusMorphism<Lambda, BlackBoxLabel>>,
    simple_pieces: HashMap<BlackBoxLabel, T>,
    main: BlackBoxLabel,
    dag: DiGraph<BlackBoxLabel, ()>,
}

impl<BlackBoxLabel, Lambda, T> FrobeniusSystem<BlackBoxLabel, Lambda, T>
where
    BlackBoxLabel: std::hash::Hash + Eq + Copy + std::fmt::Debug,
    Lambda: Eq + Copy + std::fmt::Debug,
    T: Frobenius<Lambda, BlackBoxLabel> + Clone,
{
    #[allow(dead_code)]
    pub fn new(_main_name: BlackBoxLabel) -> Self {
        todo!("new frobenius system")
    }

    #[allow(dead_code)]
    pub fn add_definition(
        &mut self,
        _new_name: BlackBoxLabel,
        _new_def: Either<FrobeniusMorphism<Lambda, BlackBoxLabel>, T>,
    ) {
        todo!("add a definition for a black boxed morphism that is either directly a T or a general Frobenius with black boxes to be filled with earlier definitions")
    }

    #[allow(dead_code)]
    pub fn set_main(&mut self, main_name: BlackBoxLabel) {
        self.main = main_name;
    }

    #[allow(dead_code)]
    fn interpret_nomut(&self, interpret_target: Option<BlackBoxLabel>) -> Result<T, String> {
        let which_interpreting = interpret_target.unwrap_or(self.main);
        if let Some(simple_answer) = self.simple_pieces.get(&which_interpreting) {
            return Ok(simple_answer.clone());
        }
        let complicated_answer = self.composite_pieces.get(&which_interpreting);
        if let Some(complicated_answer_2) = complicated_answer {
            let black_box_interpreter = |bb: &BlackBoxLabel, _src: &[Lambda], _tgt: &[Lambda]| {
                let simple_answer = self
                    .simple_pieces
                    .get(bb)
                    .ok_or(format!("No filling for {:?}", bb))
                    .map(|z| z.clone());
                if simple_answer.is_err() {
                    self.interpret_nomut(Some(*bb))
                } else {
                    simple_answer
                }
            };
            T::interpret(complicated_answer_2, &black_box_interpreter).map_err(
                |internal_explanation| {
                    format!(
                        "When doing {:?}\n{}",
                        which_interpreting, internal_explanation
                    )
                },
            )
        } else {
            Err(format!("No {:?} found", which_interpreting))
        }
    }

    #[allow(dead_code)]
    fn interpret_mut(&mut self, interpret_target: Option<BlackBoxLabel>) -> Result<T, String> {
        let which_interpreting = interpret_target.unwrap_or(self.main);
        if let Some(simple_answer) = self.simple_pieces.get(&which_interpreting) {
            return Ok(simple_answer.clone());
        }
        let resolution_order = toposort(&self.dag, None);
        if let Ok(ordered) = resolution_order {
            for cur_node in ordered {
                let node_name = self.dag.node_weight(cur_node);
                if let Some(my_bb) = node_name {
                    let cur_answer = self.interpret_nomut(Some(*my_bb));
                    if let Ok(real_cur_answer) = cur_answer.clone() {
                        let _ = self.composite_pieces.remove(my_bb);
                        self.simple_pieces.insert(*my_bb, real_cur_answer);
                    }
                    if *my_bb == which_interpreting {
                        return cur_answer;
                    }
                } else {
                    return Err(format!(
                        "Node {:?} not found after topological sort",
                        cur_node
                    ));
                }
            }
            Err(format!(
                "Through all but never found {:?}",
                which_interpreting
            ))
        } else {
            Err("Not acyclic dependencies".to_string())
        }
    }
}