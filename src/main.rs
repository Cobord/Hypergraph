use either::Either::{Left, Right};
use petgraph::dot::Dot;
use std::convert::identity;
use union_find::{QuickUnionUf, UnionBySize};

mod utils;
use utils::either_f;
mod cospan;
mod named_cospan;
use named_cospan::NamedCospan;
mod finset;
#[allow(unused_imports)]
use finset::{OrderPresInj,OrderPresSurj,Decomposition};
mod frobenius;
mod wiring_diagram;

fn main() {
    let mut x =
        NamedCospan::<u32, &'static str, &'static str>::new(vec![], vec![], vec![], vec![], vec![]);
    x.add_boundary_node_unknown_target(0, Right("out1"));
    x.add_boundary_node_known_target(0, Right("out2"));
    x.add_boundary_node_known_target(0, Left("in1"));

    let (_, _, _, graph) = x.to_graph(
        |lambda| ((), lambda),
        |port_name| either_f(port_name, identity, identity),
    );

    println!("{:?}", Dot::new(&graph));
}
