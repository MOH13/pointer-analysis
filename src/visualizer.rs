use std::fmt::{self, Display, Formatter};
use std::fs;
use std::io;
use std::ops::Deref;

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

pub fn visualize(graph: &impl Graph, path: &str) -> io::Result<()> {
    let mut buf = vec![];
    dot::render(&(graph,), &mut buf)?;
    let mut out = String::from_utf8(buf).unwrap();
    // Improves compatibility
    out = out.replace("][", " ");
    fs::write(path, out)
}
