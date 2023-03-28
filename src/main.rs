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
use finset::{Decomposition, OrderPresInj, OrderPresSurj};
mod frobenius;
use frobenius::{special_frobenius_morphism, FrobeniusMorphism, FrobeniusOperation};
mod wiring_diagram;
use wiring_diagram::WiringDiagram;

use crate::wiring_diagram::InOut;

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
    let counit_spider: FrobeniusMorphism<(), ()> = special_frobenius_morphism(1, 0, ());
    let exp_counit_spider = FrobeniusMorphism::single_op(FrobeniusOperation::Counit(()));
    assert!(exp_counit_spider == counit_spider);
    assert_eq!(counit_spider.source_types(), vec![()]);
    assert_eq!(counit_spider.target_types(), vec![]);

    let unchanged_right_names = vec![
        (InOut::In, 0),
        (InOut::Out, 1),
        (InOut::In, 2),
        (InOut::Out, 3),
        (InOut::Out, 4),
    ];
    let _example: WiringDiagram<_, (), _> = WiringDiagram::new(
        vec![],
        vec![0, 1, 2, 2, 0],
        vec![true, true, false],
        vec![],
        unchanged_right_names,
    );
}
