#![feature(is_sorted, return_position_impl_trait_in_trait)]
use either::Either::{Left, Right};
use petgraph::dot::Dot;
use union_find::{QuickUnionUf, UnionBySize};

mod category;
mod utils;
use category::ComposableMutating;
mod cospan;
mod monoidal;
mod named_cospan;
mod span;
mod symmetric_monoidal;
use named_cospan::NamedCospan;
mod finset;
#[allow(unused_imports)]
use finset::{Decomposition, OrderPresInj, OrderPresSurj};
mod frobenius;
use frobenius::{special_frobenius_morphism, FrobeniusMorphism, FrobeniusOperation};
mod wiring_diagram;
use wiring_diagram::WiringDiagram;

use crate::wiring_diagram::InOut;

mod linear_combination;
mod temperley_lieb;

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
    let counit_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(1, 0, ());
    let exp_counit_spider: FrobeniusMorphism<_, _> = FrobeniusOperation::Counit(()).into();
    assert!(exp_counit_spider == counit_spider);
    assert_eq!(counit_spider.domain(), vec![()]);
    assert_eq!(counit_spider.codomain(), vec![]);

    let unchanged_right_names = vec![
        (InOut::In, 0),
        (InOut::Out, 1),
        (InOut::In, 2),
        (InOut::Out, 3),
        (InOut::Out, 4),
    ];
    let _example: WiringDiagram<_, (), _> = WiringDiagram::new(NamedCospan::new(
        vec![],
        vec![0, 1, 2, 2, 0],
        vec![true, true, false],
        vec![],
        unchanged_right_names,
    ));
}
