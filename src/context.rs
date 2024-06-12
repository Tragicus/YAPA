use std::collections::HashMap;
use petgraph::Graph;
use petgraph::adj::*;
use crate::term::*;

#[derive(Clone)]
pub struct Context {
    pub types: HashMap<String, Term>,
    pub universes: Graph<(), bool>,
}

impl Context {
    pub fn new() -> Self {
        Context {
            types: HashMap::new(),
            universes: Graph::new(),
        }
    }

    pub fn fresh_universe(&mut self) -> usize {
        self.universes.add_node(()).index()
    }

    pub fn add_univ_constraint(&mut self, n: usize, m: usize, strict: bool) -> () {
        self.universes.update_edge(NodeIndex::new(n), NodeIndex::new(m), strict);
    }
}

