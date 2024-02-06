// https://arxiv.org/pdf/2107.13433.pdf

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use either::Either;
use petgraph::stable_graph::{NodeIndex, StableDiGraph};
use petgraph::Graph;

enum HierarchicalHypergraphError<VLabel, ELabel> {
    VertexPresent(VLabel),
    VertexNotPresent(VLabel),
    EdgePresent(Option<ELabel>),
    EdgeNotPresent(Option<ELabel>),
    InconsistentComponents(Option<ELabel>, VLabel, VLabel),
    UnconnectedHyperedge(Option<ELabel>),
    LabellersMismatch,
}

// TODO change to less overkill version
type MyTree<T> = StableDiGraph<T, ()>;

type HyperedgeSide<T> = Vec<T>;

struct HierarchicalHypergraph<VType, EType, VLabel, ELabel>
where
    VType: PartialEq + Eq + Hash + Clone,
    EType: PartialEq + Eq + Hash + Clone,
{
    vertices: HashSet<VType>,
    hyper_edges: HashMap<EType, (HyperedgeSide<VType>, HyperedgeSide<VType>)>,
    hyper_edges_src_sink: HashMap<EType, (HyperedgeSide<VType>,HyperedgeSide<VType>)>,
    v_label: fn(&VType) -> VLabel,
    e_label: fn(&EType) -> Option<ELabel>,
    constituent_hypergraphs: MyTree<Option<EType>>,
    hyperedge_to_constituent: HashMap<Option<EType>, NodeIndex>,
    vertex_to_constituent: HashMap<VType, NodeIndex>,
    constituent_to_vertices: HashMap<NodeIndex, HashSet<VType>>,
}

impl<VType, EType, VLabel, ELabel> HierarchicalHypergraph<VType, EType, VLabel, ELabel>
where
    VType: PartialEq + Eq + Hash + Clone,
    EType: PartialEq + Eq + Hash + Clone,
    VLabel: Clone,
    ELabel: Clone,
{
    #[allow(dead_code)]
    fn new(v_label: fn(&VType) -> VLabel, e_label: fn(&EType) -> Option<ELabel>) -> Self {
        let mut constituent_hypergraphs = StableDiGraph::with_capacity(1, 0);
        let top_node = constituent_hypergraphs.add_node(None);
        let mut hyperedge_to_constituent = HashMap::new();
        let _ = hyperedge_to_constituent.insert(None, top_node);
        Self {
            vertices: HashSet::new(),
            hyper_edges: HashMap::new(),
            hyper_edges_src_sink: HashMap::new(),
            v_label,
            e_label,
            constituent_hypergraphs,
            hyperedge_to_constituent,
            vertex_to_constituent: HashMap::new(),
            constituent_to_vertices: HashMap::new(),
        }
    }

    #[allow(dead_code)]
    fn vertices_check(&self) -> bool {
        let check_1 = self
            .constituent_to_vertices
            .values()
            .map(|v| v.len())
            .sum::<usize>()
            == self.vertices.len();
        if !check_1 || self.vertex_to_constituent.len() != self.vertices.len() {
            false
        } else {
            self.vertices.iter().all(|cur_vertex| {
                let my_idx = self.vertex_to_constituent.get(cur_vertex).copied();
                my_idx.is_some_and(|actual_idx| {
                    self.constituent_to_vertices
                        .get(&actual_idx)
                        .is_some_and(|v_set| v_set.contains(cur_vertex))
                })
            })
        }
    }

    #[allow(dead_code)]
    fn hyperedge_check(&self) -> bool {
        if self.hyperedge_to_constituent.len() != self.constituent_hypergraphs.node_count() {
            false
        } else {
            let check_1 = || {
                self.hyperedge_to_constituent.iter().all(|(a, b)| {
                    self.constituent_hypergraphs
                        .node_weight(*b)
                        .is_some_and(|z| z == a)
                })
            };
            let check_2 = || {
                self.hyper_edges.keys().all(|cur_key| {
                    self.hyperedge_to_constituent
                        .contains_key(&Some(cur_key.clone()))
                })
            };
            check_1() && check_2()
        }
    }

    #[allow(dead_code)]
    fn hyperedge_vertices_check(&self) -> bool {
        for (cur_hyperedge, (sources, targets)) in &self.hyper_edges {
            let cur_hyperedge_idx = self
                .hyperedge_to_constituent
                .get(&Some(cur_hyperedge.clone()));
            if let Some(real_cur_hyperedge_idx) = cur_hyperedge_idx {
                let mut my_parent = self
                    .constituent_hypergraphs
                    .neighbors_directed(*real_cur_hyperedge_idx, petgraph::Direction::Incoming);
                if let Some(real_my_parent) = my_parent.next() {
                    if my_parent.next().is_some() {
                        return false;
                    }
                    if sources
                        .iter()
                        .all(|z| self.vertex_to_constituent.get(z).cloned() != Some(real_my_parent))
                        || targets.iter().all(|z| {
                            self.vertex_to_constituent.get(z).cloned() != Some(real_my_parent)
                        })
                    {
                        return false;
                    }
                } else {
                    return false;
                }
            } else {
                // cur_hyperedge better be in the graph
                return false;
            }
        }
        true
    }

    #[allow(dead_code)]
    fn add_vertex(
        &mut self,
        new_vertex: VType,
        parent_hyper_edge: Option<EType>,
    ) -> Result<(), HierarchicalHypergraphError<VLabel, ELabel>> {
        if self.vertices.contains(&new_vertex) {
            let present_label = (self.v_label)(&new_vertex);
            return Err(HierarchicalHypergraphError::<_, ELabel>::VertexPresent(
                present_label,
            ));
        }
        if let Some(x) = self.hyperedge_to_constituent.get(&parent_hyper_edge) {
            self.vertex_to_constituent.insert(new_vertex.clone(), *x);
            if !self.constituent_to_vertices.contains_key(x) {
                self.constituent_to_vertices.insert(*x, HashSet::new());
            }
            self.constituent_to_vertices
                .get_mut(x)
                .map(|z| z.insert(new_vertex.clone()));
            self.vertices.insert(new_vertex);
            Ok(())
        } else {
            // that black box is not actually present
            let missing_edge_label = parent_hyper_edge
                .and_then(|real_parent_hyper_edge| (self.e_label)(&real_parent_hyper_edge));
            Err(HierarchicalHypergraphError::<_, _>::EdgeNotPresent(
                missing_edge_label,
            ))
        }
    }

    #[allow(dead_code)]
    fn add_nullary_hyperedge(
        &mut self,
        new_hyperedge: EType,
        parent_hyperedge: Option<EType>,
    ) -> Result<(), HierarchicalHypergraphError<VLabel, ELabel>> {
        if self.hyper_edges.contains_key(&new_hyperedge) {
            let present_label = (self.e_label)(&new_hyperedge);
            return Err(HierarchicalHypergraphError::<_, _>::EdgePresent(
                present_label,
            ));
        }
        if let Some(parent_hyperedge_loc) = self.hyperedge_to_constituent.get(&parent_hyperedge) {
            self.hyper_edges
                .insert(new_hyperedge.clone(), (Vec::new(), Vec::new()));
            self.hyper_edges_src_sink
                .insert(new_hyperedge.clone(), (Vec::new(), Vec::new()));
            let new_idx = self
                .constituent_hypergraphs
                .add_node(Some(new_hyperedge.clone()));
            self.constituent_hypergraphs
                .add_edge(*parent_hyperedge_loc, new_idx, ());
            self.hyperedge_to_constituent
                .insert(Some(new_hyperedge), new_idx);
            self.constituent_to_vertices.insert(new_idx, HashSet::new());
            Ok(())
        } else {
            let missing_label = parent_hyperedge.and_then(|z| ((self.e_label)(&z)));
            Err(HierarchicalHypergraphError::<_, _>::EdgeNotPresent(
                missing_label,
            ))
        }
    }

    #[allow(dead_code)]
    fn add_hyperedge(
        &mut self,
        new_hyperedge: EType,
        sources: impl Iterator<Item = VType> + ExactSizeIterator,
        targets: impl Iterator<Item = VType> + ExactSizeIterator,
    ) -> Result<(), HierarchicalHypergraphError<VLabel, ELabel>> {
        if self.hyper_edges.contains_key(&new_hyperedge) {
            let present_label = (self.e_label)(&new_hyperedge);
            return Err(HierarchicalHypergraphError::<_, _>::EdgePresent(
                present_label,
            ));
        }
        let mut real_sources = Vec::with_capacity(sources.len());
        let mut common_component: Option<(NodeIndex, VLabel)> = None;
        for cur_source in sources {
            self.vertices.get(&cur_source).ok_or_else(|| {
                let missing_label = (self.v_label)(&cur_source);
                HierarchicalHypergraphError::<_, ELabel>::VertexNotPresent(missing_label)
            })?;
            if common_component.is_none() {
                let component_idx = self
                    .vertex_to_constituent
                    .get(&cur_source)
                    .copied()
                    .ok_or_else(|| {
                        let missing_label = (self.v_label)(&cur_source);
                        HierarchicalHypergraphError::<_, ELabel>::VertexNotPresent(missing_label)
                    })?;
                let my_first_vertex_label = (self.v_label)(&cur_source);
                common_component = Some((component_idx, my_first_vertex_label));
            } else if let Some((component_idx, ref my_first_vertex_label)) = common_component {
                if !(self
                    .vertex_to_constituent
                    .get(&cur_source)
                    .copied()
                    .is_some_and(|z| z == component_idx))
                {
                    let edge_label = (self.e_label)(&new_hyperedge);
                    let cur_vertex_label = (self.v_label)(&cur_source);
                    return Err(
                        HierarchicalHypergraphError::<_, ELabel>::InconsistentComponents(
                            edge_label,
                            my_first_vertex_label.clone(),
                            cur_vertex_label,
                        ),
                    );
                }
            }
            real_sources.push(cur_source);
        }
        let mut real_targets = Vec::with_capacity(targets.len());
        for cur_target in targets {
            self.vertices.get(&cur_target).ok_or_else(|| {
                let missing_label = (self.v_label)(&cur_target);
                HierarchicalHypergraphError::<_, ELabel>::VertexNotPresent(missing_label)
            })?;
            if common_component.is_none() {
                let component_idx = self
                    .vertex_to_constituent
                    .get(&cur_target)
                    .copied()
                    .ok_or_else(|| {
                        let missing_label = (self.v_label)(&cur_target);
                        HierarchicalHypergraphError::<_, ELabel>::VertexNotPresent(missing_label)
                    })?;
                let my_first_vertex_label = (self.v_label)(&cur_target);
                common_component = Some((component_idx, my_first_vertex_label));
            } else if let Some((component_idx, ref my_first_vertex_label)) = common_component {
                if !(self
                    .vertex_to_constituent
                    .get(&cur_target)
                    .copied()
                    .is_some_and(|z| z == component_idx))
                {
                    let edge_label = (self.e_label)(&new_hyperedge);
                    let cur_vertex_label = (self.v_label)(&cur_target);
                    return Err(
                        HierarchicalHypergraphError::<_, ELabel>::InconsistentComponents(
                            edge_label,
                            my_first_vertex_label.clone(),
                            cur_vertex_label,
                        ),
                    );
                }
            }
            real_targets.push(cur_target);
        }
        if let Some((x, _)) = common_component {
            self.hyper_edges
                .insert(new_hyperedge.clone(), (real_sources, real_targets));
            let new_idx = self
                .constituent_hypergraphs
                .add_node(Some(new_hyperedge.clone()));
            self.constituent_hypergraphs.add_edge(x, new_idx, ());
            self.hyperedge_to_constituent
                .insert(Some(new_hyperedge), new_idx);
            self.constituent_to_vertices.insert(new_idx, HashSet::new());
            Ok(())
        } else {
            let edge_label = (self.e_label)(&new_hyperedge);
            Err(HierarchicalHypergraphError::<_, _>::UnconnectedHyperedge(
                edge_label,
            ))
        }
    }

    #[allow(dead_code)]
    fn drain_internals(
        &mut self,
        which_hyperedge: EType,
    ) -> Result<Self, HierarchicalHypergraphError<VLabel, ELabel>> {
        #[allow(unused_mut, unused_variables)]
        let mut drained = Self::new(self.v_label, self.e_label);
        if !self
            .hyperedge_to_constituent
            .contains_key(&Some(which_hyperedge.clone()))
        {
            let missing_edge_label = (self.e_label)(&which_hyperedge);
            return Err(HierarchicalHypergraphError::<_, _>::EdgeNotPresent(
                missing_edge_label,
            ));
        }
        todo!()
    }

    #[allow(dead_code)]
    fn graft_internal(
        &mut self,
        other: &Self,
        which_hyperedge_me: EType,
        which_hyperedge_other: Option<EType>,
    ) -> Result<(), HierarchicalHypergraphError<VLabel, ELabel>> {
        if self.e_label != other.e_label || self.v_label != other.v_label {
            return Err(HierarchicalHypergraphError::<_, _>::LabellersMismatch);
        }
        let cur_idx_other = *other
            .hyperedge_to_constituent
            .get(&which_hyperedge_other)
            .ok_or_else(|| {
                let missing_edge_label = which_hyperedge_other
                    .clone()
                    .and_then(|z| (other.e_label)(&z));
                HierarchicalHypergraphError::<_, _>::EdgeNotPresent(missing_edge_label)
            })?;
        let vertices_on_this_layer = other
            .constituent_to_vertices
            .get(&cur_idx_other)
            .ok_or_else(|| {
                let missing_edge_label = which_hyperedge_other
                    .clone()
                    .and_then(|z| (other.e_label)(&z));
                HierarchicalHypergraphError::<_, _>::EdgeNotPresent(missing_edge_label)
            })?;
        for cur_vertex in vertices_on_this_layer {
            self.add_vertex(cur_vertex.clone(), Some(which_hyperedge_me.clone()))?;
        }
        let hyperedges_on_this_layer = other.constituent_hypergraphs.neighbors(cur_idx_other);
        for cur_hyperedge_idx in hyperedges_on_this_layer {
            let cur_hyperedge = other
                .constituent_hypergraphs
                .node_weight(cur_hyperedge_idx)
                .cloned()
                .ok_or_else(|| {
                    // cur_hyperedge_idx is a node of other by construction
                    unreachable!("cur_hyperedge_idx is a node of other by construction");
                })?
                .ok_or_else(|| {
                    unreachable!("A child node is not the top by construction");
                })?;
            if let Some((cur_sources, cur_targets)) = other.hyper_edges.get(&cur_hyperedge) {
                self.add_hyperedge(
                    cur_hyperedge.clone(),
                    cur_sources.iter().cloned(),
                    cur_targets.iter().cloned(),
                )?;
                self.graft_internal(other, cur_hyperedge.clone(), Some(cur_hyperedge))?;
            } else {
                let missing_edge_label = which_hyperedge_other
                    .clone()
                    .and_then(|z| (other.e_label)(&z));
                return Err(HierarchicalHypergraphError::<_, _>::EdgeNotPresent(
                    missing_edge_label,
                ));
            }
        }
        Ok(())
    }

    fn outermost_line_graph(&self, _keep_nullaries: bool) -> Graph<Either<VType, EType>, ()> {
        todo!()
    }

    #[allow(dead_code)]
    fn is_connected(&self) -> bool {
        petgraph::algo::connected_components(&self.outermost_line_graph(false)) == 1
    }

    #[allow(dead_code)]
    fn is_hypernet(&self) -> bool {
        todo!()
    }
}

// TODO compose with above and the L_a on each of the EType with e_label None
// corresponds to some F equiv (L_a -o _) in order to give the correct in/outputs
// from the ones that are determined purely from inside that hyperedge
//struct WellTypedHierarchicalHypernet {}

mod test_setup {
    #[derive(PartialEq, Eq, Hash, Clone)]
    pub enum NodeLabels {
        A(bool),
        B2C(bool),
        B,
        C,
    }
    #[allow(dead_code)]
    pub fn v_label(x: &NodeLabels) -> String {
        match x {
            NodeLabels::A(_) => "A".to_string(),
            NodeLabels::B2C(_) => "B -o C".to_string(),
            NodeLabels::B => "B".to_string(),
            NodeLabels::C => "C".to_string(),
        }
    }
    #[derive(PartialEq, Eq, Hash, Clone)]
    pub enum EdgeLabel {
        F,
        EV,
        Black,
    }
    #[allow(dead_code)]
    pub fn e_label(x: &EdgeLabel) -> Option<String> {
        match x {
            EdgeLabel::F => Some("f".to_string()),
            EdgeLabel::EV => Some("ev".to_string()),
            EdgeLabel::Black => None,
        }
    }
}

mod test {
    use super::{
        test_setup::{EdgeLabel, NodeLabels},
        HierarchicalHypergraph,
    };

    #[test]
    fn in_paper_example() {
        use super::test_setup::{e_label, v_label};
        use super::HierarchicalHypergraph;
        use crate::assert_err;

        let mut example = HierarchicalHypergraph::new(v_label, e_label);
        let mut valid;
        valid = example.add_vertex(NodeLabels::A(true), None);
        assert!(valid.is_ok());
        assert!(example.vertices_check());
        valid = example.add_vertex(NodeLabels::A(true), None);
        assert_err!(valid);
        assert!(example.vertices_check());
        valid = example.add_vertex(NodeLabels::B2C(true), None);
        assert!(valid.is_ok());
        assert!(example.vertices_check());
        valid = example.add_hyperedge(
            EdgeLabel::Black,
            [NodeLabels::A(true)].into_iter(),
            [NodeLabels::B2C(true)].into_iter(),
        );
        assert!(valid.is_ok());
        assert!(example.vertices_check());

        valid = example.add_vertex(NodeLabels::A(false), Some(EdgeLabel::Black));
        assert!(valid.is_ok());
        valid = example.add_vertex(NodeLabels::B, Some(EdgeLabel::Black));
        assert!(valid.is_ok());
        valid = example.add_vertex(NodeLabels::C, Some(EdgeLabel::Black));
        assert!(valid.is_ok());
        valid = example.add_vertex(NodeLabels::B2C(false), Some(EdgeLabel::Black));
        assert!(valid.is_ok());
        valid = example.add_hyperedge(
            EdgeLabel::F,
            [NodeLabels::A(false)].into_iter(),
            [NodeLabels::B2C(false)].into_iter(),
        );
        assert!(valid.is_ok());
        valid = example.add_hyperedge(
            EdgeLabel::EV,
            [NodeLabels::B2C(false), NodeLabels::B].into_iter(),
            [NodeLabels::C].into_iter(),
        );
        assert!(valid.is_ok());

        check_paper_example(&example);
    }

    #[test]
    fn graft_paper_example() {
        use super::test_setup::{e_label, v_label};
        use super::HierarchicalHypergraph;
        use crate::assert_err;

        let mut example = HierarchicalHypergraph::new(v_label, e_label);
        let mut valid;
        valid = example.add_vertex(NodeLabels::A(true), None);
        assert!(valid.is_ok());
        assert!(example.vertices_check());
        valid = example.add_vertex(NodeLabels::A(true), None);
        assert_err!(valid);
        assert!(example.vertices_check());
        valid = example.add_vertex(NodeLabels::B2C(true), None);
        assert!(valid.is_ok());
        assert!(example.vertices_check());
        valid = example.add_hyperedge(
            EdgeLabel::Black,
            [NodeLabels::A(true)].into_iter(),
            [NodeLabels::B2C(true)].into_iter(),
        );
        assert!(valid.is_ok());
        assert!(example.vertices_check());

        let mut example_black = HierarchicalHypergraph::new(v_label, e_label);
        valid = example_black.add_vertex(NodeLabels::A(false), None);
        assert!(valid.is_ok());
        valid = example_black.add_vertex(NodeLabels::B, None);
        assert!(valid.is_ok());
        valid = example_black.add_vertex(NodeLabels::C, None);
        assert!(valid.is_ok());
        valid = example_black.add_vertex(NodeLabels::B2C(false), None);
        assert!(valid.is_ok());
        valid = example_black.add_hyperedge(
            EdgeLabel::F,
            [NodeLabels::A(false)].into_iter(),
            [NodeLabels::B2C(false)].into_iter(),
        );
        assert!(valid.is_ok());
        valid = example_black.add_hyperedge(
            EdgeLabel::EV,
            [NodeLabels::B2C(false), NodeLabels::B].into_iter(),
            [NodeLabels::C].into_iter(),
        );
        assert!(valid.is_ok());

        let graft_problem = example.graft_internal(&example_black, EdgeLabel::Black, None);
        assert!(graft_problem.is_ok());

        check_paper_example(&example);
    }

    #[allow(dead_code)]
    fn check_paper_example(
        example: &HierarchicalHypergraph<NodeLabels, EdgeLabel, String, String>,
    ) {
        let outside_idx = *example.hyperedge_to_constituent.get(&None).unwrap();
        let f_idx = *example
            .hyperedge_to_constituent
            .get(&Some(EdgeLabel::F))
            .unwrap();
        let ev_idx = *example
            .hyperedge_to_constituent
            .get(&Some(EdgeLabel::EV))
            .unwrap();
        let black_idx = *example
            .hyperedge_to_constituent
            .get(&Some(EdgeLabel::Black))
            .unwrap();
        assert!(example
            .constituent_hypergraphs
            .contains_edge(outside_idx, black_idx));
        assert!(example
            .constituent_hypergraphs
            .contains_edge(black_idx, f_idx));
        assert!(example
            .constituent_hypergraphs
            .contains_edge(black_idx, ev_idx));
        assert_eq!(example.constituent_hypergraphs.edge_count(), 3);
        assert_eq!(
            example.hyperedge_to_constituent.get(&None),
            Some(&outside_idx)
        );
        assert_eq!(
            example.hyperedge_to_constituent.get(&Some(EdgeLabel::F)),
            Some(&f_idx)
        );
        assert_eq!(
            example.hyperedge_to_constituent.get(&Some(EdgeLabel::EV)),
            Some(&ev_idx)
        );
        assert_eq!(
            example
                .hyperedge_to_constituent
                .get(&Some(EdgeLabel::Black)),
            Some(&black_idx)
        );

        assert_eq!(
            example.vertex_to_constituent.get(&NodeLabels::A(true)),
            Some(&outside_idx)
        );
        assert_eq!(
            example.vertex_to_constituent.get(&NodeLabels::B2C(true)),
            Some(&outside_idx)
        );
        assert!(example
            .constituent_to_vertices
            .get(&outside_idx)
            .unwrap()
            .contains(&NodeLabels::A(true)));
        assert!(example
            .constituent_to_vertices
            .get(&outside_idx)
            .unwrap()
            .contains(&NodeLabels::B2C(true)));
        assert_eq!(
            example
                .constituent_to_vertices
                .get(&outside_idx)
                .unwrap()
                .len(),
            2
        );
        assert_eq!(
            example.vertex_to_constituent.get(&NodeLabels::A(false)),
            Some(&black_idx)
        );
        assert_eq!(
            example.vertex_to_constituent.get(&NodeLabels::B2C(false)),
            Some(&black_idx)
        );
        assert_eq!(
            example.vertex_to_constituent.get(&NodeLabels::B),
            Some(&black_idx)
        );
        assert_eq!(
            example.vertex_to_constituent.get(&NodeLabels::C),
            Some(&black_idx)
        );
        assert!(example
            .constituent_to_vertices
            .get(&black_idx)
            .unwrap()
            .contains(&NodeLabels::A(false)));
        assert!(example
            .constituent_to_vertices
            .get(&black_idx)
            .unwrap()
            .contains(&NodeLabels::B2C(false)));
        assert!(example
            .constituent_to_vertices
            .get(&black_idx)
            .unwrap()
            .contains(&NodeLabels::B));
        assert!(example
            .constituent_to_vertices
            .get(&black_idx)
            .unwrap()
            .contains(&NodeLabels::C));
        assert_eq!(
            example
                .constituent_to_vertices
                .get(&black_idx)
                .unwrap()
                .len(),
            4
        );
        assert_eq!(
            example.constituent_to_vertices.get(&f_idx).unwrap().len(),
            0
        );
        assert_eq!(
            example.constituent_to_vertices.get(&ev_idx).unwrap().len(),
            0
        );
        assert!(example.vertices_check());
        assert!(example.hyperedge_check());
        assert!(example.hyperedge_vertices_check());

        assert!(
            example.hyper_edges.get(&EdgeLabel::Black)
                == Some(&(vec![NodeLabels::A(true)], vec![NodeLabels::B2C(true)]))
        );
        assert!(
            example.hyper_edges.get(&EdgeLabel::EV)
                == Some(&(
                    vec![NodeLabels::B2C(false), NodeLabels::B],
                    vec![NodeLabels::C]
                ))
        );
        assert!(
            example.hyper_edges.get(&EdgeLabel::F)
                == Some(&(vec![NodeLabels::A(false)], vec![NodeLabels::B2C(false)]))
        );
    }
}
