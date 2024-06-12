use bitvec::vec::BitVec;
use hashbrown::HashMap;

use super::{IntegerTerm, OnlyOnceStack};

pub fn scc(
    edges: &impl SccEdges,
    initial_nodes: Vec<IntegerTerm>,
    mut visit_handler: impl FnMut(IntegerTerm, &mut OnlyOnceStack),
) -> SccResult {
    let node_count = edges.node_count();

    let to_visit = OnlyOnceStack::from_nodes(initial_nodes, node_count);

    let mut internal_state = SccResult {
        node_count,
        iteration: 0,
        d: vec![0; node_count],
        r: vec![None; node_count],
        c: bitvec::bitvec![0; node_count],
        s: vec![],
        to_visit,
        top_order: vec![],
    };

    while let Some(v) = internal_state.to_visit.pop() {
        if internal_state.d[v as usize] == 0 {
            visit(&mut internal_state, edges, &mut visit_handler, v);
        }
    }

    internal_state
}

fn visit(
    internal: &mut SccResult,
    edges: &impl SccEdges,
    visit_handler: &mut impl FnMut(IntegerTerm, &mut OnlyOnceStack),
    v: IntegerTerm,
) {
    if internal.d[v as usize] != 0 {
        return;
    }
    visit_handler(v, &mut internal.to_visit);

    internal.iteration += 1;
    internal.d[v as usize] = internal.iteration;
    internal.r[v as usize] = Some(v);

    // let edges_iter = match internal.direction {
    //     SccDirection::Forward => Either::Left(visit_state.edges.subset[v as usize].iter()),
    //     SccDirection::Backward => Either::Right(
    //         visit_state.edges.rev_subset[v as usize]
    //             .iter()
    //             .map(|w| (w, visit_state.edges.subset[*w as usize].get(&v).unwrap())),
    //     ),
    // };

    for (w, edge_weights) in edges.successors(v) {
        if edge_weights == SccEdgeWeight::Weighted {
            internal.to_visit.push(w);
            continue;
        }

        if internal.d[w as usize] == 0 {
            visit(internal, edges, visit_handler, w);
        }
        if !internal.c[w as usize] {
            let r_v = internal.r[v as usize].unwrap();
            let r_w = internal.r[w as usize].unwrap();
            internal.r[v as usize] = Some(if internal.d[r_v as usize] < internal.d[r_w as usize] {
                r_v
            } else {
                r_w
            });
        }
    }

    if internal.r[v as usize] == Some(v) {
        internal.c.set(v as usize, true);
        while let Some(&w) = internal.s.last() {
            if internal.d[w as usize] <= internal.d[v as usize] {
                break;
            }
            internal.s.pop();
            internal.c.set(w as usize, true);
            internal.r[w as usize] = Some(v);
        }
        internal.top_order.push(v);
    } else {
        internal.s.push(v);
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum CollapseMode {
    On,
    Off,
}

pub struct SccResult {
    node_count: usize,
    iteration: usize,
    /// 0 means not visited.
    d: Vec<usize>,
    r: Vec<Option<IntegerTerm>>,
    c: BitVec,
    s: Vec<IntegerTerm>,
    to_visit: OnlyOnceStack,
    top_order: Vec<IntegerTerm>,
}

impl SccResult {
    pub fn collapse_cycles(mut self, graph: &mut impl SccGraph) -> Vec<IntegerTerm> {
        let mut nodes = vec![];
        let mut components: HashMap<IntegerTerm, (IntegerTerm, u32)> = HashMap::new();
        for v in 0..self.node_count as u32 {
            if let Some(r_v) = self.r[v as usize] {
                let v_heuristic = graph.parent_heuristic(v);
                if v_heuristic == 0 {
                    continue;
                }
                nodes.push((v, r_v));
                if let Err(mut cur) = components.try_insert(r_v, (v, v_heuristic)) {
                    let (cur_best, best_heuristic) = cur.entry.get_mut();
                    if v_heuristic > *best_heuristic {
                        *cur_best = v;
                        *best_heuristic = v_heuristic;
                    }
                }
            }
        }
        for (v, r_v) in nodes {
            let &(rep, _) = components.get(&r_v).unwrap();
            if v != rep {
                graph.unify(v, |w| {
                    let Some(r) = self.r[w as usize] else {
                        return w;
                    };
                    components.get(&r).map(|(rep, _)| *rep).unwrap_or(w)
                });
            }
        }

        self.top_order
    }

    pub fn into_top_order(self) -> Vec<IntegerTerm> {
        self.top_order
    }
}

#[derive(PartialEq, Eq)]
pub enum SccEdgeWeight {
    Unweighted,
    Weighted,
    Both,
}

pub trait SccGraph {
    fn unify(&mut self, child: IntegerTerm, parent_fn: impl Fn(IntegerTerm) -> IntegerTerm);
    fn parent_heuristic(&self, node: IntegerTerm) -> u32;
}

pub trait SccEdges {
    fn node_count(&self) -> usize;
    fn successors(&self, node: IntegerTerm) -> impl Iterator<Item = (IntegerTerm, SccEdgeWeight)>;
    fn collapse_mode(&self) -> CollapseMode;
}
