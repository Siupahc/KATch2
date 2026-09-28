//! Minimize -- heuristically minimize netkat automata.
//!
//! This has three parts:
//!
//!  1. Identify conflicts
//!  2. Graph coloring
//!  3. Merge the states!

use crate::expr::{Exp, Expr};
use crate::holes::aut::{self, DFA, ENFA, ExplicitDFA, NFA, ops};
use crate::sp;
use crate::spp::{self, reduce};
use petgraph::algo::{coloring, dominators, tarjan_scc};
use petgraph::graph::{DiGraph, NodeIndex, UnGraph};
use petgraph::unionfind::UnionFind;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Step 1 -- taking an automaton and identifying (un)mergable states
///
/// Two states are mergable if any packet that reaches both of them has the same behavior when
/// progressing from either of them.
///
/// Concretely, we take the intersection `R` of the reaching sets of both, and check that the
/// automata rooted at `q` and at `r` (with start packets restricted to `R`) have empty symmetric
/// difference.
fn are_mergable(
    dfa: &ExplicitDFA,
    reachable_sets: &HashMap<usize, sp::SP>,
    store: &mut spp::SPPstore,
    q: usize,
    r: usize,
) -> bool {
    let reach_q = reachable_sets.get(&q).copied().unwrap_or(store.sp.zero);
    let reach_r = reachable_sets.get(&r).copied().unwrap_or(store.sp.zero);
    let shared = store.sp.intersect(reach_q, reach_r);
    if shared == store.sp.zero {
        return true;
    }

    let filter = store.ibwd(shared);
    let at_q = Rooted {
        dfa,
        root: q,
        filter,
    };
    let at_r = Rooted {
        dfa,
        root: r,
        filter,
    };
    let sym_diff = ops::union(
        ops::intersection(&at_q, ops::complement(&at_r)),
        ops::intersection(ops::complement(&at_q), &at_r),
    );
    aut::is_empty(&sym_diff, store)
}

/// State of [`Rooted`]: the fresh root, or a state of the underlying DFA.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum RootedState {
    Root,
    Inner(usize),
}

/// `dfa`, but starting at state `root`, and only accepting start packets in the input set of
/// `filter` (an SPP of the form `ibwd(sp)`).
///
/// The root is a fresh copy of `root`, so that if the run later comes back to `root` it is no
/// longer restricted.
struct Rooted<'a> {
    dfa: &'a ExplicitDFA,
    root: usize,
    filter: spp::SPP,
}

impl ENFA for Rooted<'_> {
    type State = RootedState;

    fn start(&self, _store: &mut spp::SPPstore) -> RootedState {
        RootedState::Root
    }

    fn is_visible(&self, _store: &mut spp::SPPstore, _q: &RootedState) -> bool {
        true
    }

    fn transitions(
        &self,
        store: &mut spp::SPPstore,
        q: &RootedState,
    ) -> Vec<(spp::SPP, RootedState)> {
        match *q {
            RootedState::Root => self.dfa.transitions[self.root]
                .iter()
                .filter_map(|&(spp, next)| {
                    let restricted = store.intersect(self.filter, spp);
                    (restricted != store.zero).then_some((restricted, RootedState::Inner(next)))
                })
                .collect(),
            RootedState::Inner(s) => self.dfa.transitions[s]
                .iter()
                .map(|&(spp, next)| (spp, RootedState::Inner(next)))
                .collect(),
        }
    }

    fn output(&self, store: &mut spp::SPPstore, q: &RootedState) -> spp::SPP {
        match *q {
            RootedState::Root => store.intersect(self.filter, self.dfa.outputs[self.root]),
            RootedState::Inner(s) => self.dfa.outputs[s],
        }
    }
}

impl NFA for Rooted<'_> {}
impl DFA for Rooted<'_> {}

/// Step 2 -- graph coloring.
///
/// Construct a graph with an edge indicating that two states *cannot* be merged, and compute a
/// coloring. This will be the new small set of states: one new state per color.
///
/// Dead states (that no packet reaches) are discarded: they get no color. The merged automaton never
/// has an edge to them anyway, since its edges only carry packets that reach their target.
///
/// Return (coloring, number of colors).
fn coloring(
    dfa: &ExplicitDFA,
    reachable_sets: &HashMap<usize, sp::SP>,
    store: &mut spp::SPPstore,
) -> (HashMap<usize, usize>, usize) {
    let live: Vec<usize> = (0..dfa.num_states())
        .filter(|q| reachable_sets.get(q).is_some_and(|&r| r != store.sp.zero))
        .collect();

    // Node `i` of the conflict graph is state `live[i]`. Add every node up front: `from_edges`
    // alone would drop states with no conflicts
    let mut conflicts: UnGraph<(), (), usize> = UnGraph::default();
    for _ in &live {
        conflicts.add_node(());
    }
    conflicts.extend_with_edges(
        (0..live.len())
            .flat_map(|i| (0..i).map(move |j| (i, j)))
            .filter(|&(i, j)| !are_mergable(dfa, reachable_sets, store, live[i], live[j])),
    );

    let (coloring, _) = coloring::dsatur_coloring(&conflicts);
    let coloring: HashMap<usize, usize> = coloring
        .into_iter()
        .map(|(id, c)| (live[id.index()], c))
        .collect();

    split_colors(&live, reachable_sets, store, &coloring)
}

/// Split each color into groups of states with disjoint reachability sets.
///
/// If the states of one color can be partitioned into `Q1` and `Q2` such that no packet reaches
/// both a state in `Q1` and a state in `Q2`, then there's no need to merge them, so we give `Q1`
/// and `Q2` separate colors. Concretely, the groups are the connected components of the "reaching
/// sets overlap" relation within each color.
///
/// Return (coloring, number of colors).
fn split_colors(
    live: &[usize],
    reachable_sets: &HashMap<usize, sp::SP>,
    store: &mut spp::SPPstore,
    coloring: &HashMap<usize, usize>,
) -> (HashMap<usize, usize>, usize) {
    // Union-find over indices into `live`
    let mut groups = UnionFind::<usize>::new(live.len());
    for (i, &q) in live.iter().enumerate() {
        for (j, &r) in live[..i].iter().enumerate() {
            if coloring[&q] == coloring[&r]
                && store.sp.intersect(reachable_sets[&q], reachable_sets[&r]) != store.sp.zero
            {
                groups.union(i, j);
            }
        }
    }

    // Number the groups densely, in order of their first state
    let mut group_color: HashMap<usize, usize> = HashMap::new();
    let new_coloring: HashMap<usize, usize> = live
        .iter()
        .enumerate()
        .map(|(i, &q)| {
            let next = group_color.len();
            (q, *group_color.entry(groups.find_mut(i)).or_insert(next))
        })
        .collect();
    (new_coloring, group_color.len())
}

/// Step 3 -- building the smaller automaton
///
/// Each color becomes one state. For each incoming packet, the new state behaves like one of the
/// old states of that color which that packet can reach (the first one, in state order). Since
/// states of the same color are pairwise mergable, it doesn't matter which one we pick, and picking
/// just one keeps the transitions disjoint.
fn merge_states(
    dfa: &ExplicitDFA,
    reachable_sets: &HashMap<usize, sp::SP>,
    store: &mut spp::SPPstore,
) -> ExplicitDFA {
    let (coloring, colors) = coloring(dfa, reachable_sets, store);

    let mut members: Vec<Vec<usize>> = vec![Vec::new(); colors];
    for q in 0..dfa.num_states() {
        if let Some(&c) = coloring.get(&q) {
            members[c].push(q);
        }
    }

    let mut transitions = Vec::with_capacity(colors);
    let mut outputs = Vec::with_capacity(colors);
    for states in &members {
        // Packets already handled by an earlier member of this color
        let mut covered = store.sp.zero;
        // Transitions, merged by target color
        let mut trans: HashMap<usize, spp::SPP> = HashMap::new();
        let mut output = store.zero;

        for &q in states {
            let reach_q = reachable_sets.get(&q).copied().unwrap_or(store.sp.zero);
            let owned = store.sp.difference(reach_q, covered);
            if owned == store.sp.zero {
                continue;
            }
            covered = store.sp.union(covered, owned);
            let filter = store.ibwd(owned);

            for &(spp, next) in &dfa.transitions[q] {
                let restricted = store.intersect(filter, spp);
                if restricted != store.zero {
                    // Some packet reaching `q` takes this edge, so `next` is not dead
                    let target = coloring[&next];
                    let prev = trans.get(&target).copied().unwrap_or(store.zero);
                    let merged = store.union(prev, restricted);
                    trans.insert(target, merged);
                }
            }
            let out = store.intersect(filter, dfa.outputs[q]);
            output = store.union(output, out);
        }

        let mut trans: Vec<(spp::SPP, usize)> = trans
            .into_iter()
            .map(|(target, spp)| (spp, target))
            .collect();
        trans.sort_by_key(|&(_, target)| target);

        // Simplify the edges and output: only packets that reach this state matter.
        //
        // To keep the edges disjoint (so this is still a DFA), each edge must also be zero wherever
        // an earlier (already simplified) edge is nonzero. Later edges need no special treatment:
        // they are nonzero only on reaching packets, where every edge is kept exact.
        let care = store.ibwd(covered);
        let mut taken = store.zero;
        for (spp, _) in &mut trans {
            let edge_care = store.union(care, taken);
            *spp = reduce::reduce(store, *spp, edge_care);
            taken = store.union(taken, *spp);
        }
        let output = reduce::reduce(store, output, care);

        transitions.push(trans);
        outputs.push(output);
    }

    ExplicitDFA {
        start: coloring[&dfa.start],
        transitions,
        outputs,
    }
}

pub fn minimize(dfa: &ExplicitDFA, store: &mut spp::SPPstore) -> ExplicitDFA {
    let reachable = aut::compute_reachable(dfa, store);
    merge_states(dfa, &reachable, store)
}

/// Convert a DFA to an equivalent NetKAT expression: [`minimize`] it, then use [`to_expr_tarjan`].
///
/// In simple testing (the `minimize_shrinks_exprs` test), this was the best configuration:
/// minimizing first never gave a larger expression, and on bigger random inputs it made them several
/// times smaller. After minimizing, Tarjan's algorithm gave slightly smaller expressions than Kleene
/// state elimination.
pub fn to_expr(dfa: &ExplicitDFA, store: &mut spp::SPPstore) -> Exp {
    let small = minimize(dfa, store);
    to_expr_tarjan(&small, store)
}

/// Convert a DFA to an equivalent NetKAT expression, by Kleene state elimination.
///
/// We build the edge-labelled NFA described in [`ExpNfa::from_dfa`], then eliminate the DFA's
/// states one at a time, until only the edge from initial to final is left.
///
/// States are eliminated greedily, picking the one that increases the number of edges the least.
/// Eliminating `q` adds an edge for each (incoming, outgoing) pair, and removes the incoming,
/// outgoing, and self-loop edges of `q`.
pub fn to_expr_kleene(dfa: &ExplicitDFA, store: &mut spp::SPPstore) -> Exp {
    let mut nfa = ExpNfa::from_dfa(dfa, store);

    let mut remaining: BTreeSet<usize> = (0..dfa.num_states()).collect();
    while let Some(q) = remaining
        .iter()
        .copied()
        .min_by_key(|&q| nfa.elimination_cost(q))
    {
        nfa.eliminate(q);
        remaining.remove(&q);
    }

    nfa.edges[nfa.initial]
        .remove(&nfa.fin)
        .unwrap_or_else(Expr::zero)
}

/// Convert a DFA to an equivalent NetKAT expression, by Tarjan's path expression algorithm.
///
/// We build the edge-labelled NFA described in [`ExpNfa::from_dfa`], and compute the path
/// expression from its initial state to its final state. Following Tarjan ("Fast algorithms for
/// solving path problems", 1981), we use the dominator tree to split the problem into one small
/// problem per node of the tree:
///
/// - `path(q)` is all paths from the initial state to `q`. Every such path passes through
///   `idom(q)`, and after its last visit to `idom(q)` it stays among the nodes dominated by
///   `idom(q)`. So `path(q) = path(idom(q)); dpath(q)`, where `dpath(q)` is all paths from `idom(q)`
///   to `q` that stay strictly below `idom(q)`. Hence `path(final)` is the product of `dpath`
///   down the dominator tree.
/// - `dpath` is computed for the children of each node `v` together, bottom-up (see
///   [`solve_siblings`]).
pub fn to_expr_tarjan(dfa: &ExplicitDFA, store: &mut spp::SPPstore) -> Exp {
    let nfa = ExpNfa::from_dfa(dfa, store);
    let num_nodes = nfa.edges.len();

    let mut graph: DiGraph<(), (), usize> = DiGraph::default();
    for _ in 0..num_nodes {
        graph.add_node(());
    }
    for (p, out) in nfa.edges.iter().enumerate() {
        for &r in out.keys() {
            graph.add_edge(NodeIndex::new(p), NodeIndex::new(r), ());
        }
    }
    let doms = dominators::simple_fast(&graph, NodeIndex::new(nfa.initial));
    // `None` for the initial state and for unreachable states
    let idom: Vec<Option<usize>> = (0..num_nodes)
        .map(|q| {
            doms.immediate_dominator(NodeIndex::new(q))
                .map(|d| d.index())
        })
        .collect();
    if idom[nfa.fin].is_none() {
        return Expr::zero();
    }

    let mut children = vec![Vec::new(); num_nodes];
    for (q, &d) in idom.iter().enumerate() {
        if let Some(d) = d {
            children[d].push(q);
        }
    }

    // Post-order, so that `dpath` is known for every node strictly below `v` when we get to `v`
    let mut dpath = vec![Expr::zero(); num_nodes];
    for v in post_order(&children, nfa.initial) {
        solve_siblings(&nfa, &idom, v, &children[v], &mut dpath);
    }

    let mut chain = vec![];
    let mut q = nfa.fin;
    while q != nfa.initial {
        chain.push(q);
        q = idom[q].unwrap();
    }
    chain.iter().rev().fold(Expr::one(), |acc, &q| {
        Expr::sequence_simp(acc, dpath[q].clone())
    })
}

/// Compute `dpath` for the dominator tree children `kids` of `v`, given `dpath` for every node
/// below them.
///
/// A path from `v` to a child `c` that stays below `v` starts with an edge from `v` to some child
/// `c'`, then moves between the subtrees of the children. It can only enter a child's subtree at
/// the child itself (since the child dominates its subtree), so it is a sequence of hops `c' ~> c''`,
/// each of which wanders around the subtree of `c'` and then takes an edge to `c''`. The hops are
/// the edges of the *derived graph* on `kids`, and the hops from `c'` that end with the edge
/// `u -> c''` are `dpath(D2); ...; dpath(Dk); dpath(u); label(u -> c'')`, where
/// `c', D2, ..., Dk, u` is the dominator tree path from `c'` down to `u`.
///
/// This gives the (left-linear) system `dpath(c) = label(v -> c) + Σ_c' dpath(c'); hops(c' -> c)`.
/// We solve it by Gauss-Jordan elimination, visiting the children in topological order of the
/// derived graph's strongly connected components. So we only need Kleene stars for the children
/// that are actually in a cycle of the derived graph; for the others, elimination just substitutes
/// forwards.
fn solve_siblings(
    nfa: &ExpNfa,
    idom: &[Option<usize>],
    v: usize,
    kids: &[usize],
    dpath: &mut [Exp],
) {
    let k = kids.len();
    let index: HashMap<usize, usize> = kids.iter().enumerate().map(|(i, &c)| (c, i)).collect();

    // `b[j]` is the edge from `v` to `kids[j]`, and `a[i][j]` is the hops from `kids[i]` to `kids[j]`
    let mut b: Vec<Exp> = kids
        .iter()
        .map(|c| nfa.edges[v].get(c).cloned().unwrap_or_else(Expr::zero))
        .collect();
    let mut a: Vec<Vec<Exp>> = vec![vec![Expr::zero(); k]; k];
    for (j, &c) in kids.iter().enumerate() {
        for &u in &nfa.incoming[c] {
            // Skip the edge from `v` (already in `b`), and edges from unreachable states
            if u == v || idom[u].is_none() {
                continue;
            }
            let mut hop = nfa.edges[u][&c].clone();
            let mut w = u;
            while idom[w] != Some(v) {
                hop = Expr::sequence_simp(dpath[w].clone(), hop);
                w = idom[w].unwrap();
            }
            let i = index[&w];
            a[i][j] = Expr::union_simp(std::mem::replace(&mut a[i][j], Expr::zero()), hop);
        }
    }

    // `tarjan_scc` lists the components in reverse topological order
    let mut derived: DiGraph<(), (), usize> = DiGraph::default();
    for _ in 0..k {
        derived.add_node(());
    }
    for (i, row) in a.iter().enumerate() {
        for (j, hop) in row.iter().enumerate() {
            if **hop != Expr::Zero {
                derived.add_edge(NodeIndex::new(i), NodeIndex::new(j), ());
            }
        }
    }
    let order: Vec<usize> = tarjan_scc(&derived)
        .into_iter()
        .rev()
        .flatten()
        .map(|n| n.index())
        .collect();

    let is_zero = |e: &Exp| **e == Expr::Zero;
    for &i in &order {
        // Solve equation `i` for `x_i` by Arden's rule: `x_i = (b_i + Σ_{j≠i} x_j; a_ji); a_ii*`
        let loop_star = Expr::star_simp(std::mem::replace(&mut a[i][i], Expr::zero()));
        if *loop_star != Expr::One {
            b[i] = Expr::sequence_simp(b[i].clone(), loop_star.clone());
            for row in a.iter_mut() {
                if !is_zero(&row[i]) {
                    row[i] = Expr::sequence_simp(row[i].clone(), loop_star.clone());
                }
            }
        }
        // Substitute `x_i` into every other equation that mentions it
        for l in 0..k {
            if l == i || is_zero(&a[i][l]) {
                continue;
            }
            let a_il = std::mem::replace(&mut a[i][l], Expr::zero());
            let via_i = Expr::sequence_simp(b[i].clone(), a_il.clone());
            b[l] = Expr::union_simp(b[l].clone(), via_i);
            for (j, row) in a.iter_mut().enumerate() {
                if j != i && !is_zero(&row[i]) {
                    let via_i = Expr::sequence_simp(row[i].clone(), a_il.clone());
                    row[l] = Expr::union_simp(row[l].clone(), via_i);
                }
            }
        }
    }

    for (j, &c) in kids.iter().enumerate() {
        dpath[c] = std::mem::replace(&mut b[j], Expr::zero());
    }
}

/// Post-order traversal of the tree given by `children`, starting from `root`.
fn post_order(children: &[Vec<usize>], root: usize) -> Vec<usize> {
    let mut order = vec![];
    let mut stack = vec![(root, false)];
    while let Some((q, expanded)) = stack.pop() {
        if expanded {
            order.push(q);
        } else {
            stack.push((q, true));
            stack.extend(children[q].iter().map(|&c| (c, false)));
        }
    }
    order
}

/// An NFA with edges labelled by expressions, for [`to_expr_kleene`] and [`to_expr_tarjan`].
/// Parallel edges are merged into one by union, so there is at most one edge between each
/// (ordered) pair of states.
struct ExpNfa {
    /// `edges[p][r]` is the label of the edge from `p` to `r`.
    edges: Vec<BTreeMap<usize, Exp>>,
    /// `incoming[r]` is the set of `p` with an edge from `p` to `r`.
    incoming: Vec<BTreeSet<usize>>,
    /// A fresh state with no incoming edges.
    initial: usize,
    /// A fresh state with no outgoing edges.
    fin: usize,
}

impl ExpNfa {
    /// A DFA transition `(spp, next)` means "apply `spp`, record the new packet in the trace, then
    /// continue from `next`", so each state `q` denotes
    ///
    /// ```text
    /// E_q = output_q + Σ spp; dup; E_next
    /// ```
    ///
    /// So the NFA has the DFA's states, plus a fresh initial state with a `1` edge to the start
    /// state, an edge `spp; dup` per transition, and an edge `output_q` from each state to a fresh
    /// final state. The DFA denotes the sum of all paths from initial to final.
    fn from_dfa(dfa: &ExplicitDFA, store: &mut spp::SPPstore) -> ExpNfa {
        let n = dfa.num_states();
        let mut nfa = ExpNfa {
            edges: vec![BTreeMap::new(); n + 2],
            incoming: vec![BTreeSet::new(); n + 2],
            initial: n,
            fin: n + 1,
        };

        nfa.add_edge(nfa.initial, dfa.start, Expr::one());
        for q in 0..n {
            for &(spp, next) in &dfa.transitions[q] {
                let label = Expr::sequence_simp(store.to_expr(spp), Expr::dup());
                nfa.add_edge(q, next, label);
            }
            let output = store.to_expr(dfa.outputs[q]);
            nfa.add_edge(q, nfa.fin, output);
        }
        nfa
    }

    fn add_edge(&mut self, from: usize, to: usize, label: Exp) {
        if *label == Expr::Zero {
            return;
        }
        let label = match self.edges[from].remove(&to) {
            Some(prev) => Expr::union_simp(prev, label),
            None => label,
        };
        self.edges[from].insert(to, label);
        self.incoming[to].insert(from);
    }

    /// Change in the number of edges from eliminating `q`.
    fn elimination_cost(&self, q: usize) -> isize {
        let has_loop = self.edges[q].contains_key(&q);
        let num_in = self.incoming[q].len() - has_loop as usize;
        let num_out = self.edges[q].len() - has_loop as usize;
        (num_in * num_out) as isize - (num_in + num_out + has_loop as usize) as isize
    }

    /// Remove `q`, replacing each path `p -> q -> r` by an edge `p -> r`.
    fn eliminate(&mut self, q: usize) {
        let mut outgoing = std::mem::take(&mut self.edges[q]);
        let self_loop = outgoing
            .remove(&q)
            .map(Expr::star_simp)
            .unwrap_or_else(Expr::one);
        let incoming = std::mem::take(&mut self.incoming[q]);

        for &r in outgoing.keys() {
            self.incoming[r].remove(&q);
        }
        for &p in &incoming {
            if p == q {
                continue;
            }
            let into_q = self.edges[p].remove(&q).unwrap();
            for (&r, out_of_q) in &outgoing {
                let label = Expr::sequence_simp(
                    Expr::sequence_simp(into_q.clone(), self_loop.clone()),
                    out_of_q.clone(),
                );
                self.add_edge(p, r, label);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// True iff `a` and `b` accept exactly the same traces.
    fn equivalent(store: &mut spp::SPPstore, a: &ExplicitDFA, b: &ExplicitDFA) -> bool {
        let sym_diff = ops::union(
            ops::intersection(a, ops::complement(b)),
            ops::intersection(ops::complement(a), b),
        );
        aut::is_empty(&sym_diff, store)
    }

    type ToExpr = fn(&ExplicitDFA, &mut spp::SPPstore) -> Exp;

    /// Round trip `expr -> DFA -> (minimize?) -> expr -> DFA`, and check the language is preserved.
    fn fuzz_to_expr(seed: u64, do_minimize: bool, to_expr: ToExpr) {
        crate::fuzz::seed_fuzzer(seed);
        let expr_depth = 3;
        let num_fields = 2;

        for trial in 0..200 {
            let (expr, _) = crate::fuzz::genax(0, expr_depth, num_fields);
            let mut store = spp::SPPstore::new(num_fields);
            let dfa = aut::expr_to_dfa(&expr, &mut store);
            let dfa = if do_minimize {
                minimize(&dfa, &mut store)
            } else {
                dfa
            };

            let back = to_expr(&dfa, &mut store);
            let dfa_back = aut::expr_to_dfa(&back, &mut store);
            assert!(
                equivalent(&mut store, &dfa, &dfa_back),
                "to_expr changed the language on trial {trial}\n  expr: {expr}\n  back: {back}"
            );
        }
    }

    #[test]
    fn fuzz_to_expr_roundtrip() {
        fuzz_to_expr(0x5EED_0015, false, to_expr);
    }

    #[test]
    fn fuzz_to_expr_kleene_roundtrip() {
        fuzz_to_expr(0x5EED_0011, false, to_expr_kleene);
    }

    #[test]
    fn fuzz_minimize_to_expr_kleene_roundtrip() {
        fuzz_to_expr(0x5EED_0012, true, to_expr_kleene);
    }

    #[test]
    fn fuzz_to_expr_tarjan_roundtrip() {
        fuzz_to_expr(0x5EED_0013, false, to_expr_tarjan);
    }

    #[test]
    fn fuzz_minimize_to_expr_tarjan_roundtrip() {
        fuzz_to_expr(0x5EED_0014, true, to_expr_tarjan);
    }

    #[test]
    fn fuzz_minimize_preserves_language() {
        crate::fuzz::seed_fuzzer(0x5EED_0010);
        let expr_depth = 4;
        let num_fields = 3;

        for trial in 0..300 {
            let (expr, _) = crate::fuzz::genax(0, expr_depth, num_fields);
            let mut aut = crate::aut::Aut::new(num_fields);
            let state = aut.expr_to_state(&expr);
            let dfa = aut::aut_to_dfa(&mut aut, state);
            let store = aut.spp_store_mut();

            let small = minimize(&dfa, store);
            assert!(
                small.num_states() <= dfa.num_states(),
                "minimize grew the automaton on trial {trial} for expr {expr}"
            );
            assert!(
                equivalent(store, &dfa, &small),
                "minimize changed the language on trial {trial} for expr {expr}"
            );
            for (q, trans) in small.transitions.iter().enumerate() {
                for (i, &(a, _)) in trans.iter().enumerate() {
                    for &(b, _) in &trans[..i] {
                        assert_eq!(
                            store.intersect(a, b),
                            store.zero,
                            "overlapping edges out of state {q} on trial {trial} for expr {expr}"
                        );
                    }
                }
            }
        }
    }

    /// Number of nodes in the syntax tree of `e`.
    fn expr_size(e: &Expr) -> usize {
        match e {
            Expr::Union(a, b)
            | Expr::Intersect(a, b)
            | Expr::Xor(a, b)
            | Expr::Difference(a, b)
            | Expr::Sequence(a, b)
            | Expr::LtlUntil(a, b) => 1 + expr_size(a) + expr_size(b),
            Expr::Star(a) | Expr::Complement(a) | Expr::TestNegation(a) | Expr::LtlNext(a) => {
                1 + expr_size(a)
            }
            Expr::IfThenElse(a, b, c) => 1 + expr_size(a) + expr_size(b) + expr_size(c),
            _ => 1,
        }
    }

    /// Does converting to an expression give smaller results after minimizing?
    ///
    /// Not a real test, just prints statistics. Run with
    /// `cargo test --release --lib minimize_shrinks_exprs -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn minimize_shrinks_exprs() {
        let algorithms: [(&str, ToExpr); 2] =
            [("kleene", to_expr_kleene), ("tarjan", to_expr_tarjan)];
        for (expr_depth, num_fields) in [(3, 2), (4, 3), (5, 3)] {
            crate::fuzz::seed_fuzzer(0x5EED_0020);
            let trials = 300;
            let mut states = [0, 0];
            let mut totals = [[0usize; 2]; 2];
            let mut smaller = [0; 2];
            let mut larger = [0; 2];
            let mut log_ratio = [0.0f64; 2];

            for _ in 0..trials {
                let (expr, _) = crate::fuzz::genax(0, expr_depth, num_fields);
                let mut store = spp::SPPstore::new(num_fields);
                let dfa = aut::expr_to_dfa(&expr, &mut store);
                let small = minimize(&dfa, &mut store);
                states[0] += dfa.num_states();
                states[1] += small.num_states();

                for (k, (_, to_expr)) in algorithms.iter().enumerate() {
                    let before = expr_size(&to_expr(&dfa, &mut store));
                    let after = expr_size(&to_expr(&small, &mut store));
                    totals[k][0] += before;
                    totals[k][1] += after;
                    smaller[k] += (after < before) as usize;
                    larger[k] += (after > before) as usize;
                    log_ratio[k] += (after as f64 / before as f64).ln();
                }
            }

            println!(
                "depth {expr_depth}, {num_fields} fields, {trials} trials: states {} -> {}",
                states[0], states[1]
            );
            for (k, (name, _)) in algorithms.iter().enumerate() {
                println!(
                    "  {name}: total size {} -> {}, smaller in {}, larger in {}, \
                     geometric mean ratio {:.3}",
                    totals[k][0],
                    totals[k][1],
                    smaller[k],
                    larger[k],
                    (log_ratio[k] / trials as f64).exp()
                );
            }
        }
    }
}
