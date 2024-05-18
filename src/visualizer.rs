use std::fmt::{self, Display, Formatter};
use std::fs;
use std::io;
use std::marker::PhantomData;
use std::ops::Deref;

use hashbrown::HashSet;

use std::fmt::Debug;
use std::hash::Hash;

use crate::solver::{Solver, SolverExt, SolverInput, SolverSolution};

#[derive(Clone)]
pub struct Edge<N, W> {
    pub from: Node<N>,
    pub to: Node<N>,
    pub weight: W,
    pub kind: EdgeKind,
}

#[derive(Clone, Copy)]
pub enum EdgeKind {
    Subset,
    Inclusion,
    CondRight,
    CondLeft,
}

#[derive(Clone)]
pub struct Node<N> {
    pub inner: N,
    pub id: usize,
}

impl<N> Deref for Node<N> {
    type Target = N;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<N: Display> Display for Node<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

#[derive(Clone, Copy)]
pub struct OffsetWeight(pub u32);

impl Display for OffsetWeight {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.0 == 0 {
            Ok(())
        } else {
            write!(f, "{}", self.0)
        }
    }
}

pub trait Graph {
    type Node: Display + Clone;
    type Weight: Display + Clone;

    fn nodes(&self) -> Vec<Node<Self::Node>>;
    fn edges(&self) -> Vec<Edge<Self::Node, Self::Weight>>;
}

impl<'a, T, N, W> dot::Labeller<'a, Node<N>, Edge<N, W>> for (&T,)
where
    T: Graph<Node = N, Weight = W>,
    N: Display,
    W: Display,
{
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("Result_Graph").unwrap()
    }

    fn node_id(&'a self, n: &Node<N>) -> dot::Id<'a> {
        dot::Id::new(format!("n{}", n.id)).unwrap()
    }

    fn node_label(&'a self, n: &Node<N>) -> dot::LabelText<'a> {
        dot::LabelText::label(n.inner.to_string())
    }

    fn edge_label(&'a self, e: &Edge<N, W>) -> dot::LabelText<'a> {
        dot::LabelText::label(e.weight.to_string())
    }

    fn edge_style(&'a self, e: &Edge<N, W>) -> dot::Style {
        match e.kind {
            EdgeKind::Subset => dot::Style::Solid,
            EdgeKind::Inclusion | EdgeKind::CondRight | EdgeKind::CondLeft => dot::Style::Dashed,
        }
    }

    fn edge_color(&'a self, e: &Edge<N, W>) -> Option<dot::LabelText<'a>> {
        match e.kind {
            EdgeKind::Inclusion => Some(dot::LabelText::label("green")),
            _ => None,
        }
    }

    fn edge_end_arrow(&'a self, e: &Edge<N, W>) -> dot::Arrow {
        match e.kind {
            EdgeKind::CondRight => {
                dot::Arrow::from_arrow(dot::ArrowShape::Inv(dot::Fill::Filled, dot::Side::Both))
            }
            _ => {
                dot::Arrow::from_arrow(dot::ArrowShape::Normal(dot::Fill::Filled, dot::Side::Both))
            }
        }
    }
}

impl<'a, T, N, W> dot::GraphWalk<'a, Node<N>, Edge<N, W>> for (&T,)
where
    T: Graph<Node = N, Weight = W>,
    N: Clone,
    W: Clone,
{
    fn nodes(&'a self) -> dot::Nodes<'a, Node<N>> {
        Graph::nodes(self.0).into()
    }

    fn edges(&'a self) -> dot::Edges<'a, Edge<N, W>> {
        Graph::edges(self.0).into()
    }

    fn source(&'a self, edge: &Edge<N, W>) -> Node<N> {
        edge.from.clone()
    }

    fn target(&'a self, edge: &Edge<N, W>) -> Node<N> {
        edge.to.clone()
    }
}

pub trait Visualizable {
    fn visualize(&self, path: &str) -> io::Result<()>;
}

impl<G> Visualizable for G
where
    G: Graph,
{
    fn visualize(&self, path: &str) -> io::Result<()> {
        let mut buf = vec![];
        dot::render(&(self,), &mut buf)?;
        let mut out = String::from_utf8(buf).unwrap();
        // Improves compatibility
        out = out.replace("][", " ");
        fs::write(path, out)
    }
}

pub trait VisualizableSolution: SolverSolution + Visualizable {}
impl<S> VisualizableSolution for S where S: SolverSolution + Visualizable {}

pub type DynamicVisualizableSolution<'s, T> =
    Box<dyn VisualizableSolution<Term = T, TermSet = HashSet<T>> + 's>;
pub type DynamicVisualizableSolver<'s, I, T> =
    Box<dyn Solver<I, Solution = DynamicVisualizableSolution<'s, T>> + 's>;

impl<'s, T> SolverSolution for DynamicVisualizableSolution<'s, T>
where
    T: Hash + Eq + Clone + Debug,
{
    type Term = T;
    type TermSet = HashSet<T>;

    fn get(&self, node: &Self::Term) -> Self::TermSet {
        self.deref().get(node)
    }

    fn get_len(&self, node: &Self::Term) -> usize {
        self.deref().get_len(node)
    }
}

impl<'s, T> Visualizable for DynamicVisualizableSolution<'s, T>
where
    T: Hash + Eq + Clone + Debug,
{
    fn visualize(&self, path: &str) -> io::Result<()> {
        self.deref().visualize(path)
    }
}

impl<'s, I, T> Solver<I> for DynamicVisualizableSolver<'s, I, T>
where
    I: SolverInput<Term = T>,
    T: Hash + Eq + Clone + Debug,
{
    type Solution = DynamicVisualizableSolution<'s, T>;

    fn solve(&self, input: I) -> Self::Solution {
        self.deref().solve(input)
    }
}
impl<'s, I, T> SolverExt for DynamicVisualizableSolver<'s, I, T> {}

#[derive(Copy, Clone)]
pub enum Never {}

impl Display for Never {
    fn fmt(&self, _: &mut Formatter) -> fmt::Result {
        match *self {}
    }
}

pub trait AsDynamicVisualizableExt<'s> {
    fn as_dynamic_visualizable(self) -> Box<AsDynamicVisualizable<'s, Self>>
    where
        Self: Sized;
}

impl<'s, S> AsDynamicVisualizableExt<'s> for S
where
    S: SolverExt,
{
    fn as_dynamic_visualizable(self) -> Box<AsDynamicVisualizable<'s, Self>> {
        Box::new(AsDynamicVisualizable(self, PhantomData))
    }
}

pub struct AsDynamicVisualizable<'s, S>(pub S, PhantomData<&'s ()>);

impl<'s, S, I> Solver<I> for AsDynamicVisualizable<'s, S>
where
    S: Solver<I>,
    S::Solution: VisualizableSolution<Term = I::Term, TermSet = HashSet<I::Term>> + 's,
    I: SolverInput,
    I::Term: Hash + Eq + Clone + Debug,
{
    type Solution = DynamicVisualizableSolution<'s, I::Term>;

    fn solve(&self, input: I) -> Self::Solution {
        Box::new(self.0.solve(input))
    }
}

impl<'s, S> SolverExt for AsDynamicVisualizable<'s, S> {}

pub struct NotVisualizableSolution<S>(pub S);

impl<S> SolverSolution for NotVisualizableSolution<S>
where
    S: SolverSolution,
{
    type Term = S::Term;
    type TermSet = S::TermSet;

    fn get(&self, node: &Self::Term) -> Self::TermSet {
        self.0.get(node)
    }

    fn get_len(&self, node: &Self::Term) -> usize {
        self.0.get_len(node)
    }
}

impl<S> Visualizable for NotVisualizableSolution<S> {
    fn visualize(&self, _: &str) -> io::Result<()> {
        panic!("Cannot visualize a non-visualizable solution");
    }
}
