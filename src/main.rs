#![feature(is_sorted, return_position_impl_trait_in_trait)]
use either::Either::{Left, Right};
use petgraph::dot::Dot;
use union_find::{QuickUnionUf, UnionBySize};

mod utils;

mod category;
mod monoidal;
mod operadic;
mod symmetric_monoidal;

mod finset;

mod frobenius;
mod frobenius_system;

mod cospan;
mod named_cospan;
use named_cospan::NamedCospan;
mod span;
mod wiring_diagram;

mod linear_combination;
mod temperley_lieb;

mod amalgamated;
mod explicitly_gen;
mod fp_gp;
mod free_gp;

mod e1_operad;
mod e2_operad;

fn main() {
    let mut x = NamedCospan::<u32, &'static str, &'static str>::empty();
    x.add_boundary_node_unknown_target(0, Right("out1"));
    x.add_boundary_node_known_target(0, Right("out2"));
    x.add_boundary_node_known_target(0, Left("in1"));
    x.add_boundary_node_unknown_target(0, Right("out4"));
    x.add_boundary_node_unknown_target(1, Left("in2"));
    x.add_boundary_node_unknown_target(1, Left("in3"));
    x.connect_pair(Left("in2"), Left("in3"));

    let (_, _, _, graph) = x.to_graph(
        |lambda| (lambda.to_string(), ()),
        |port_type_color, port_name| {
            *port_type_color = format!("{} of type {}", port_name, *port_type_color);
        },
    );

    println!("{:?}", Dot::new(&graph));

    x.connect_pair(Right("out1"), Right("out4"));

    let (_, _, _, graph) = x.to_graph(
        |lambda| (lambda.to_string(), ()),
        |port_type_color, port_name| {
            *port_type_color = format!("{} of type {}", port_name, *port_type_color);
        },
    );

    println!("{:?}", Dot::new(&graph));
}
