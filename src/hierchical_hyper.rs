// https://arxiv.org/pdf/2107.13433.pdf

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use either::Either;
use petgraph::algo::is_cyclic_directed;
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

struct HierarchicalHypergraph<VType, EType, VLabel, ELabel, LabelAux>
where
    VType: PartialEq + Eq + Hash + Clone,
    EType: PartialEq + Eq + Hash + Clone,
{
    vertices: HashSet<VType>,
    hyper_edges: HashMap<EType, (HyperedgeSide<VType>, HyperedgeSide<VType>)>,
    v_label: fn(&VType, &LabelAux) -> VLabel,
    e_label: fn(&EType, &LabelAux) -> Option<ELabel>,
    constituent_hypergraphs: MyTree<Option<EType>>,
    hyperedge_to_constituent: HashMap<Option<EType>, NodeIndex>,
    vertex_to_constituent: HashMap<VType, NodeIndex>,
    constituent_to_vertices: HashMap<NodeIndex, HashSet<VType>>,
    label_aux: LabelAux,
}

impl<VType, EType, VLabel, ELabel, LabelAux>
    HierarchicalHypergraph<VType, EType, VLabel, ELabel, LabelAux>
where
    VType: PartialEq + Eq + Hash + Clone,
    EType: PartialEq + Eq + Hash + Clone,
    VLabel: Clone,
    ELabel: Clone,
{
    #[allow(dead_code)]
    fn new(
        v_label: fn(&VType, &LabelAux) -> VLabel,
        e_label: fn(&EType, &LabelAux) -> Option<ELabel>,
        label_aux: LabelAux,
    ) -> Self {
        let mut constituent_hypergraphs = StableDiGraph::with_capacity(1, 0);
        let top_node = constituent_hypergraphs.add_node(None);
        let mut hyperedge_to_constituent = HashMap::new();
        let _ = hyperedge_to_constituent.insert(None, top_node);
        Self {
            vertices: HashSet::new(),
            hyper_edges: HashMap::new(),
            v_label,
            e_label,
            constituent_hypergraphs,
            hyperedge_to_constituent,
            vertex_to_constituent: HashMap::new(),
            constituent_to_vertices: HashMap::new(),
            label_aux,
        }
    }

    #[allow(dead_code)]
    fn vertices_check(&self) -> bool {
        #[allow(clippy::redundant_closure_for_method_calls)]
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
        #[allow(clippy::if_not_else)]
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
                        .all(|z| self.vertex_to_constituent.get(z).copied() != Some(real_my_parent))
                    {
                        return false;
                    }
                    if targets
                        .iter()
                        .all(|z| self.vertex_to_constituent.get(z).copied() != Some(real_my_parent))
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
            let present_label = (self.v_label)(&new_vertex, &self.label_aux);
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
            let missing_edge_label = parent_hyper_edge.and_then(|real_parent_hyper_edge| {
                (self.e_label)(&real_parent_hyper_edge, &self.label_aux)
            });
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
            let present_label = (self.e_label)(&new_hyperedge, &self.label_aux);
            return Err(HierarchicalHypergraphError::<_, _>::EdgePresent(
                present_label,
            ));
        }
        if let Some(parent_hyperedge_loc) = self.hyperedge_to_constituent.get(&parent_hyperedge) {
            self.hyper_edges
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
            let missing_label =
                parent_hyperedge.and_then(|z| ((self.e_label)(&z, &self.label_aux)));
            Err(HierarchicalHypergraphError::<_, _>::EdgeNotPresent(
                missing_label,
            ))
        }
    }

    #[allow(dead_code)]
    fn add_hyperedge(
        &mut self,
        new_hyperedge: EType,
        sources: impl ExactSizeIterator<Item = VType>,
        targets: impl ExactSizeIterator<Item = VType>,
    ) -> Result<(), HierarchicalHypergraphError<VLabel, ELabel>> {
        if self.hyper_edges.contains_key(&new_hyperedge) {
            let present_label = (self.e_label)(&new_hyperedge, &self.label_aux);
            return Err(HierarchicalHypergraphError::<_, _>::EdgePresent(
                present_label,
            ));
        }
        let mut real_sources = Vec::with_capacity(sources.len());
        let mut common_component: Option<(NodeIndex, VLabel)> = None;
        for cur_source in sources {
            self.vertices.get(&cur_source).ok_or_else(|| {
                let missing_label = (self.v_label)(&cur_source, &self.label_aux);
                HierarchicalHypergraphError::<_, ELabel>::VertexNotPresent(missing_label)
            })?;
            if common_component.is_none() {
                let component_idx = self
                    .vertex_to_constituent
                    .get(&cur_source)
                    .copied()
                    .ok_or_else(|| {
                        let missing_label = (self.v_label)(&cur_source, &self.label_aux);
                        HierarchicalHypergraphError::<_, ELabel>::VertexNotPresent(missing_label)
                    })?;
                let my_first_vertex_label = (self.v_label)(&cur_source, &self.label_aux);
                common_component = Some((component_idx, my_first_vertex_label));
            } else if let Some((component_idx, ref my_first_vertex_label)) = common_component {
                if self
                    .vertex_to_constituent
                    .get(&cur_source)
                    .copied()
                    .is_none_or(|z| z != component_idx)
                {
                    let edge_label = (self.e_label)(&new_hyperedge, &self.label_aux);
                    let cur_vertex_label = (self.v_label)(&cur_source, &self.label_aux);
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
                let missing_label = (self.v_label)(&cur_target, &self.label_aux);
                HierarchicalHypergraphError::<_, ELabel>::VertexNotPresent(missing_label)
            })?;
            if common_component.is_none() {
                let component_idx = self
                    .vertex_to_constituent
                    .get(&cur_target)
                    .copied()
                    .ok_or_else(|| {
                        let missing_label = (self.v_label)(&cur_target, &self.label_aux);
                        HierarchicalHypergraphError::<_, ELabel>::VertexNotPresent(missing_label)
                    })?;
                let my_first_vertex_label = (self.v_label)(&cur_target, &self.label_aux);
                common_component = Some((component_idx, my_first_vertex_label));
            } else if let Some((component_idx, ref my_first_vertex_label)) = common_component {
                if self
                    .vertex_to_constituent
                    .get(&cur_target)
                    .copied()
                    .is_none_or(|z| z != component_idx)
                {
                    let edge_label = (self.e_label)(&new_hyperedge, &self.label_aux);
                    let cur_vertex_label = (self.v_label)(&cur_target, &self.label_aux);
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
            let edge_label = (self.e_label)(&new_hyperedge, &self.label_aux);
            Err(HierarchicalHypergraphError::<_, _>::UnconnectedHyperedge(
                edge_label,
            ))
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    #[allow(dead_code)]
    fn drain_internals(
        &mut self,
        which_hyperedge: EType,
    ) -> Result<Self, HierarchicalHypergraphError<VLabel, ELabel>>
    where
        LabelAux: Clone,
    {
        #[allow(unused_mut, unused_variables)]
        let mut drained = Self::new(self.v_label, self.e_label, self.label_aux.clone());
        if !self
            .hyperedge_to_constituent
            .contains_key(&Some(which_hyperedge.clone()))
        {
            let missing_edge_label = (self.e_label)(&which_hyperedge, &self.label_aux);
            return Err(HierarchicalHypergraphError::<_, _>::EdgeNotPresent(
                missing_edge_label,
            ));
        }
        todo!("drain a hierarchical hypergraph")
    }

    #[allow(clippy::needless_pass_by_value)]
    #[allow(dead_code)]
    fn graft_internal(
        &mut self,
        other: &Self,
        which_hyperedge_me: EType,
        which_hyperedge_other: Option<EType>,
    ) -> Result<(), HierarchicalHypergraphError<VLabel, ELabel>>
    where
        LabelAux: Eq,
    {
        if !std::ptr::fn_addr_eq(self.e_label, other.e_label)
            || !std::ptr::fn_addr_eq(self.v_label, other.v_label)
            || self.label_aux != other.label_aux
        {
            return Err(HierarchicalHypergraphError::<_, _>::LabellersMismatch);
        }
        let cur_idx_other = *other
            .hyperedge_to_constituent
            .get(&which_hyperedge_other)
            .ok_or_else(|| {
                let missing_edge_label = which_hyperedge_other
                    .clone()
                    .and_then(|z| (other.e_label)(&z, &self.label_aux));
                HierarchicalHypergraphError::<_, _>::EdgeNotPresent(missing_edge_label)
            })?;
        let vertices_on_this_layer = other
            .constituent_to_vertices
            .get(&cur_idx_other)
            .ok_or_else(|| {
                let missing_edge_label = which_hyperedge_other
                    .clone()
                    .and_then(|z| (other.e_label)(&z, &self.label_aux));
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
                    .and_then(|z| (other.e_label)(&z, &self.label_aux));
                return Err(HierarchicalHypergraphError::<_, _>::EdgeNotPresent(
                    missing_edge_label,
                ));
            }
        }
        Ok(())
    }

    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn component_line_graph(
        &self,
        keep_nullaries: bool,
        real_constituent: &NodeIndex,
    ) -> Graph<Either<VType, EType>, ()> {
        let mut to_return = Graph::new();
        let all_vertices = self.constituent_to_vertices.get(real_constituent);
        let mut vert_to_idx = HashMap::new();
        for v in all_vertices.unwrap_or(&HashSet::new()) {
            let cur_idx = to_return.add_node(either::Left(v.clone()));
            vert_to_idx.insert(v.clone(), cur_idx);
        }
        let child_hyperedges = self.constituent_hypergraphs.neighbors(*real_constituent);
        for cur_hyper in child_hyperedges {
            let cur_hyperedge = self.constituent_hypergraphs.node_weight(cur_hyper).expect(
                "
                    Already checked that it exists as a node",
            );
            if let Some(x) = cur_hyperedge {
                if let Some((src_conn, tgt_conn)) = self.hyper_edges.get(x) {
                    let nullary = src_conn.is_empty() && tgt_conn.is_empty();
                    if nullary && keep_nullaries {
                        to_return.add_node(either::Right(x.clone()));
                    } else if !nullary {
                        let hyperedge_idx = to_return.add_node(either::Right(x.clone()));
                        for src in src_conn {
                            let src_idx = vert_to_idx.get(src).expect("All the vertices have been added to the graph already. So any src/tgt of the hyperedges have node index already.");
                            to_return.add_edge(*src_idx, hyperedge_idx, ());
                        }
                        for tgt in tgt_conn {
                            let tgt_idx = vert_to_idx.get(tgt).expect("All the vertices have been added to the graph already. So any src/tgt of the hyperedges have node index already.");
                            to_return.add_edge(hyperedge_idx, *tgt_idx, ());
                        }
                    }
                } else {
                    unreachable!("Every hyperedge in the graph has it's (possibly empty) sources and targets");
                }
            } else {
                unreachable!("The None hyperedge was the parent, it is not a neighbor of anything");
            }
        }
        to_return
    }

    fn outermost_line_graph(&self, keep_nullaries: bool) -> Graph<Either<VType, EType>, ()> {
        let which_constituent = self.hyperedge_to_constituent.get(&None);
        if let Some(real_constituent) = which_constituent {
            self.component_line_graph(keep_nullaries, real_constituent)
        } else {
            unreachable!(
                "There is at least the outermost hyperedge which was present since construction"
            );
        }
    }

    #[allow(dead_code)]
    fn is_connected(&self) -> bool {
        petgraph::algo::connected_components(&self.outermost_line_graph(true)) == 1
    }

    #[allow(clippy::needless_pass_by_value)]
    fn in_out_isolated(&self, which_hyperedge: Option<EType>) -> Option<[Vec<VType>; 3]> {
        let which_constituent = self.hyperedge_to_constituent.get(&which_hyperedge)?;
        Some(self.in_out_isolated_helper(which_constituent))
    }

    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn in_out_isolated_helper(&self, which_constituent: &NodeIndex) -> [Vec<VType>; 3] {
        let graph = self.component_line_graph(false, which_constituent);
        let mut in_idces = graph
            .node_indices()
            .filter(|z| {
                graph[*z].is_left()
                    && graph
                        .neighbors_directed(*z, petgraph::Direction::Incoming)
                        .count()
                        == 0
            })
            .collect::<Vec<_>>();
        let mut out_idces = graph
            .node_indices()
            .filter(|z| {
                graph[*z].is_left()
                    && graph
                        .neighbors_directed(*z, petgraph::Direction::Outgoing)
                        .count()
                        == 0
            })
            .collect::<Vec<_>>();
        let mut isolated_vs =
            Vec::with_capacity(std::cmp::min(in_idces.len(), out_idces.len()) >> 2);
        for cur_in in &in_idces {
            if out_idces.contains(cur_in) {
                isolated_vs.push(*cur_in);
            }
        }
        in_idces.retain(|z| !out_idces.contains(z));
        out_idces.retain(|z| !in_idces.contains(z));
        [in_idces, out_idces, isolated_vs].map(|idx_list| {
            idx_list
                .into_iter()
                .map(|idx| {
                    graph
                        .node_weight(idx)
                        .expect("They are all indices in graph by construction")
                        .to_owned()
                })
                .map(|z| z.left().expect("Already chose only the left"))
                .collect()
        })
    }

    fn times_as_interface_with_multiplicity(
        &self,
        vertex: &VType,
        as_src: bool,
    ) -> Vec<(EType, usize)> {
        let which_constituent = self.vertex_to_constituent.get(vertex);
        which_constituent.map_or(vec![], |&z| {
            let possible_hyperedges = self
                .constituent_hypergraphs
                .neighbors_directed(z, petgraph::Direction::Outgoing);
            possible_hyperedges
                .filter_map(|cur_hyperedge_idx| {
                    let cur_hyperedge_type = self
                        .constituent_hypergraphs
                        .node_weight(cur_hyperedge_idx)
                        .expect("Already checked that it exists as a node");
                    if let Some(cur_edge) = cur_hyperedge_type {
                        let (srcs, tgts) = self
                            .hyper_edges
                            .get(cur_edge)
                            .expect("Already checked that it is a hyperedge");
                        let apt_vec = if as_src { srcs } else { tgts };
                        let cur_edges_count_vertex = apt_vec
                            .iter()
                            .filter(|&cur_vertex| *cur_vertex == *vertex)
                            .count();
                        if cur_edges_count_vertex == 0 {
                            None
                        } else {
                            Some((cur_edge.clone(), cur_edges_count_vertex))
                        }
                    } else {
                        unreachable!(
                            "The None hyperedge was the parent, it is not a neighbor of anything"
                        );
                    }
                })
                .collect()
        })
    }

    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn has_no_internals(&self, which_constituent: &NodeIndex) -> bool {
        let has_no_vertices = self
            .constituent_to_vertices
            .get(which_constituent)
            .expect("Should have already checked that this is an index of a hyperedge")
            .is_empty();
        let has_no_hyperedges = self
            .constituent_hypergraphs
            .neighbors(*which_constituent)
            .count()
            == 0;
        has_no_vertices && has_no_hyperedges
    }

    fn is_hypernetable(&self) -> [bool; 5] {
        /*
        to turn into a hypernet need to give the total ordering on the outermost
        inputs and outputs (that is one that is sure to effectively have a None label)
        that is to say those vertices in the outermost layer which only occur as sources if at all
        or only occur as targets if at all
        (the ones that don't occur on any hyperedge are both inputs and outputs, they are isolated vertices)
        */
        let is_acyclic = self
            .hyperedge_to_constituent
            .values()
            .all(|cur_hyperedge_idx| {
                let line_graph = self.component_line_graph(false, cur_hyperedge_idx);
                !is_cyclic_directed(&line_graph)
            });
        let any_vertex_multisource = self.vertices.iter().any(|vertex| {
            let count_with_mult = self
                .times_as_interface_with_multiplicity(vertex, true)
                .iter()
                .fold(0, |acc, elt| acc + elt.1);
            count_with_mult > 1
        });
        let any_vertex_multitarget = self.vertices.iter().any(|vertex| {
            let count_with_mult = self
                .times_as_interface_with_multiplicity(vertex, false)
                .iter()
                .fold(0, |acc, elt| acc + elt.1);
            count_with_mult > 1
        });
        let (some_labelled_idces, none_labelled_idces): (Vec<_>, Vec<_>) = self
            .hyperedge_to_constituent
            .iter()
            .partition(|(edge_type, _edge_idx)| match edge_type {
                Some(real_edge_type) => {
                    let my_label = (self.e_label)(real_edge_type, &self.label_aux);
                    my_label.is_some()
                }
                None => false,
            });
        let all_some_labelled_are_empty = some_labelled_idces
            .into_iter()
            .all(|(_edge_type, edge_idx)| self.has_no_internals(edge_idx));
        let all_none_labelled_are_nonempty = !none_labelled_idces
            .into_iter()
            .any(|(_edge_type, edge_idx)| self.has_no_internals(edge_idx));
        [
            is_acyclic,
            !any_vertex_multisource,
            !any_vertex_multitarget,
            all_some_labelled_are_empty,
            all_none_labelled_are_nonempty,
        ]
    }
}

#[allow(dead_code)]
struct WellTypedHierarchicalHypernet<VType, EType, VLabel, ELabel, LabelAux>
where
    VType: PartialEq + Eq + Hash + Clone,
    EType: PartialEq + Eq + Hash + Clone,
{
    underlying: HierarchicalHypergraph<VType, EType, VLabel, ELabel, LabelAux>,
    same_level_interface: HashMap<Option<EType>, (Vec<VType>, Vec<VType>)>,
    parents_interface: HashMap<EType, (Vec<VType>, Vec<VType>)>,
    none_labelled_lsuba_s: HashMap<EType, HyperedgeSide<VType>>,
}

#[allow(dead_code)]
enum HierarchicalHypernetError<VLabel, ELabel> {
    HasCycle,
    MultiSourceVertex,
    MultiTargetVertex,
    ASomeLabelledFull,
    ANoneLabelledEmpty,
    EdgeWithoutSameInterface(Option<ELabel>),
    EdgeWithoutParentInterface(ELabel),
    UnderlyingError(HierarchicalHypergraphError<VLabel, ELabel>),
}

impl<VType, EType, VLabel, ELabel, LabelAux>
    WellTypedHierarchicalHypernet<VType, EType, VLabel, ELabel, LabelAux>
where
    VType: PartialEq + Eq + Hash + Clone,
    EType: PartialEq + Eq + Hash + Clone,
    VLabel: Clone,
    ELabel: Clone,
{
    #[allow(dead_code)]
    fn new(
        underlying: HierarchicalHypergraph<VType, EType, VLabel, ELabel, LabelAux>,
        same_level_interface: HashMap<Option<EType>, (Vec<VType>, Vec<VType>)>,
        parents_interface: HashMap<EType, (Vec<VType>, Vec<VType>)>,
    ) -> Result<Self, HierarchicalHypernetError<VLabel, ELabel>> {
        let [is_acyclic, no_vertex_multisource, no_vertex_multitarget, all_some_labelled_are_empty, all_none_labelled_are_nonempty] =
            underlying.is_hypernetable();
        if !is_acyclic {
            return Err(HierarchicalHypernetError::<VLabel, ELabel>::HasCycle);
        }
        if !no_vertex_multisource {
            return Err(HierarchicalHypernetError::<VLabel, ELabel>::MultiSourceVertex);
        }
        if !no_vertex_multitarget {
            return Err(HierarchicalHypernetError::<VLabel, ELabel>::MultiTargetVertex);
        }
        if !all_some_labelled_are_empty {
            return Err(HierarchicalHypernetError::<VLabel, ELabel>::ASomeLabelledFull);
        }
        if !all_none_labelled_are_nonempty {
            return Err(HierarchicalHypernetError::<VLabel, ELabel>::ANoneLabelledEmpty);
        }
        #[allow(clippy::for_kv_map)]
        for (_a, _b) in &underlying.hyperedge_to_constituent {
            todo!("Check the interfaces making sure what said is on same level is and what is on parent's is actually on parents");
        }
        Ok(Self {
            underlying,
            same_level_interface,
            parents_interface,
            none_labelled_lsuba_s: HashMap::new(),
        })
    }
}

#[allow(clippy::trivially_copy_pass_by_ref)]
mod test_setup {
    #[derive(PartialEq, Eq, Hash, Clone)]
    pub enum NodeLabels {
        A(bool),
        B2C(bool),
        B,
        C,
    }
    #[allow(dead_code)]
    pub fn v_label(x: &NodeLabels, _: &()) -> String {
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
    pub fn e_label(x: &EdgeLabel, _: &()) -> Option<String> {
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

        let mut example = HierarchicalHypergraph::new(v_label, e_label, ());
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

        let mut example = HierarchicalHypergraph::new(v_label, e_label, ());
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

        let mut example_black = HierarchicalHypergraph::new(v_label, e_label, ());
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

    #[allow(clippy::too_many_lines)]
    #[allow(dead_code)]
    fn check_paper_example(
        example: &HierarchicalHypergraph<NodeLabels, EdgeLabel, String, String, ()>,
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
        assert!(
            example.times_as_interface_with_multiplicity(&NodeLabels::A(true), true)
                == vec![(EdgeLabel::Black, 1)]
        );
        assert!(
            example.times_as_interface_with_multiplicity(&NodeLabels::A(true), false) == vec![]
        );
        assert_eq!(
            example.vertex_to_constituent.get(&NodeLabels::B2C(true)),
            Some(&outside_idx)
        );
        assert!(
            example.times_as_interface_with_multiplicity(&NodeLabels::B2C(true), true) == vec![]
        );
        assert!(
            example.times_as_interface_with_multiplicity(&NodeLabels::B2C(true), false)
                == vec![(EdgeLabel::Black, 1)]
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
        assert!(
            example.times_as_interface_with_multiplicity(&NodeLabels::A(false), true)
                == vec![(EdgeLabel::F, 1)]
        );
        assert!(
            example.times_as_interface_with_multiplicity(&NodeLabels::A(false), false) == vec![]
        );
        assert_eq!(
            example.vertex_to_constituent.get(&NodeLabels::B2C(false)),
            Some(&black_idx)
        );
        assert!(
            example.times_as_interface_with_multiplicity(&NodeLabels::B2C(false), true)
                == vec![(EdgeLabel::EV, 1)]
        );
        assert!(
            example.times_as_interface_with_multiplicity(&NodeLabels::B2C(false), false)
                == vec![(EdgeLabel::F, 1)]
        );
        assert_eq!(
            example.vertex_to_constituent.get(&NodeLabels::B),
            Some(&black_idx)
        );
        assert!(
            example.times_as_interface_with_multiplicity(&NodeLabels::B, true)
                == vec![(EdgeLabel::EV, 1)]
        );
        assert!(example.times_as_interface_with_multiplicity(&NodeLabels::B, false) == vec![]);
        assert_eq!(
            example.vertex_to_constituent.get(&NodeLabels::C),
            Some(&black_idx)
        );
        assert!(example.times_as_interface_with_multiplicity(&NodeLabels::C, true) == vec![]);
        assert!(
            example.times_as_interface_with_multiplicity(&NodeLabels::C, false)
                == vec![(EdgeLabel::EV, 1)]
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

        let outer_graph = example.outermost_line_graph(true);
        let my_node_identifiers = outer_graph
            .raw_nodes()
            .iter()
            .map(|z| z.weight.clone())
            .collect::<Vec<_>>();
        for cur_v in [NodeLabels::B2C(true), NodeLabels::A(true)] {
            assert!(my_node_identifiers.contains(&either::Left(cur_v)));
        }
        for (cur_e, (cur_e_srcs, cur_e_tgts)) in [(
            EdgeLabel::Black,
            (vec![NodeLabels::A(true)], vec![NodeLabels::B2C(true)]),
        )] {
            assert!(my_node_identifiers.contains(&either::Right(cur_e.clone())));
            let cur_e_idx = outer_graph
                .node_indices()
                .find(|z| outer_graph[*z] == either::Right(cur_e.clone()))
                .unwrap();
            for cur_e_src in cur_e_srcs.clone() {
                let cur_e_src_idx = outer_graph
                    .node_indices()
                    .find(|z| outer_graph[*z] == either::Left(cur_e_src.clone()))
                    .unwrap();
                assert!(outer_graph.contains_edge(cur_e_src_idx, cur_e_idx));
            }
            for cur_e_tgt in cur_e_tgts.clone() {
                let cur_e_tgt_idx = outer_graph
                    .node_indices()
                    .find(|z| outer_graph[*z] == either::Left(cur_e_tgt.clone()))
                    .unwrap();
                assert!(outer_graph.contains_edge(cur_e_idx, cur_e_tgt_idx));
            }
            assert_eq!(
                outer_graph
                    .neighbors_directed(cur_e_idx, petgraph::Direction::Incoming)
                    .count(),
                cur_e_srcs.len()
            );
            assert_eq!(
                outer_graph
                    .neighbors_directed(cur_e_idx, petgraph::Direction::Outgoing)
                    .count(),
                cur_e_tgts.len()
            );
        }
        assert_eq!(my_node_identifiers.len(), 3);
        assert_eq!(outer_graph.edge_count(), 2);
        assert_eq!(outer_graph.node_count(), 3);
        assert!(example.is_connected());

        if let Some([ins_seen, outs_seen, isolated_seen]) = example.in_out_isolated(None) {
            assert!(ins_seen == [NodeLabels::A(true)]);
            assert!(outs_seen == [NodeLabels::B2C(true)]);
            assert!(isolated_seen.is_empty());
        } else {
            unreachable!("This is a hyperedge in example");
        }
        if let Some([ins_seen, outs_seen, isolated_seen]) =
            example.in_out_isolated(Some(EdgeLabel::Black))
        {
            assert_eq!(ins_seen.len(), 2);
            assert!(ins_seen.contains(&NodeLabels::B));
            assert!(ins_seen.contains(&NodeLabels::A(false)));
            assert!(outs_seen == [NodeLabels::C]);
            assert!(isolated_seen.is_empty());
        } else {
            unreachable!("This is a hyperedge in example");
        }
        if let Some([ins_seen, outs_seen, isolated_seen]) =
            example.in_out_isolated(Some(EdgeLabel::F))
        {
            assert!(ins_seen.is_empty());
            assert!(outs_seen.is_empty());
            assert!(isolated_seen.is_empty());
        } else {
            unreachable!("This is a hyperedge in example");
        }
        if let Some([ins_seen, outs_seen, isolated_seen]) =
            example.in_out_isolated(Some(EdgeLabel::EV))
        {
            assert!(ins_seen.is_empty());
            assert!(outs_seen.is_empty());
            assert!(isolated_seen.is_empty());
        } else {
            unreachable!("This is a hyperedge in example");
        }

        let hypernetable = example.is_hypernetable();
        assert_eq!(hypernetable, [true, true, true, true, true]);
    }
}
