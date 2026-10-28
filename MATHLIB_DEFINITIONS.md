# Mathlib definitions used in Challenge.lean (Corrádi–Hajnal)

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision. Most excerpts are the ones already
audited for the registered entries `jtraverso/chordal-split-threshold-graphs` and
`jtraverso/erdos-girth-chromatic`.

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 95:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## SimpleGraph.neighborSet

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 456:

```lean
/-- `G.neighborSet v` is the set of vertices adjacent to `v` in `G`. -/
def neighborSet (v : V) : Set V := {w | G.Adj v w}
```

## SimpleGraph.neighborFinset, SimpleGraph.degree

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, lines 169–170 and 242:

```lean
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset

def degree : ℕ := #(G.neighborFinset v)
```

## SimpleGraph.minDegree

`Mathlib/Combinatorics/SimpleGraph/Finite.lean`, lines 447–448:

```lean
def minDegree [DecidableRel G.Adj] : ℕ :=
  WithTop.untopD 0 (univ.image fun v => G.degree v).min
```

## SimpleGraph.Walk

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 54:

```lean
/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq
```

## SimpleGraph.Walk.length

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 87:

```lean
/-- The length of a walk is the number of edges/darts along it. -/
def length {u v : V} : G.Walk u v → ℕ
  | nil => 0
  | cons _ q => q.length.succ
```

## SimpleGraph.Walk.support

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 118:

```lean
/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {u v : V} : G.Walk u v → List V
  | nil => [u]
  | cons _ p => u :: p.support
```

## SimpleGraph.Walk.darts

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 123:

```lean
/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts {u v : V} : G.Walk u v → List G.Dart
  | nil => []
  | cons h p => ⟨(u, _), h⟩ :: p.darts
```

## SimpleGraph.Walk.edges

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 129:

```lean
/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `SimpleGraph.Walk.darts`. -/
def edges {u v : V} (p : G.Walk u v) : List (Sym2 V) := p.darts.map Dart.edge
```

## SimpleGraph.Walk.IsTrail

`Mathlib/Combinatorics/SimpleGraph/Paths.lean`, line 69:

```lean
/-- A *trail* is a walk with no repeating edges. -/
@[mk_iff isTrail_def]
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup
```

## SimpleGraph.Walk.IsCircuit

`Mathlib/Combinatorics/SimpleGraph/Paths.lean`, line 79:

```lean
/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
@[mk_iff isCircuit_def]
structure IsCircuit {u : V} (p : G.Walk u u) : Prop extends isTrail : IsTrail p where
  ne_nil : p ≠ nil
```

## SimpleGraph.Walk.IsCycle

`Mathlib/Combinatorics/SimpleGraph/Paths.lean`, line 84:

```lean
/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) : Prop extends isCircuit : IsCircuit p where
  support_nodup : p.support.tail.Nodup
```

## SimpleGraph.comap

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 126:

```lean
/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `SimpleGraph.induce` for a wrapper.

This is surjective when `f` is injective (see `SimpleGraph.comap_surjective`). -/
protected def comap (f : V → W) (G : SimpleGraph W) : SimpleGraph V where
  Adj u v := G.Adj (f u) (f v)
  symm.symm _ _ h := h.symm
```

## SimpleGraph.induce

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 227:

```lean
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `SimpleGraph.comap`. -/
abbrev induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)
```

## SimpleGraph.Embedding

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 300:

```lean
/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G'.Adj (f v) (f w) ↔ G.Adj v w`. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings. -/
abbrev Embedding :=
  RelEmbedding G.Adj G'.Adj
```

## SimpleGraph.IsAcyclic

`Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`, line 56:

```lean
/-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
def IsAcyclic : Prop := ∀ ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle
```

## Complete graph

[Mathlib/Combinatorics/SimpleGraph/Basic.lean:330](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Basic.lean#L330)

```lean
/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices. -/
@[wikidata Q45715]
abbrev completeGraph (V : Type u) : SimpleGraph V := ⊤
```

## Adjacency in the complete graph

[Mathlib/Combinatorics/SimpleGraph/Basic.lean:337](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Combinatorics/SimpleGraph/Basic.lean#L337)

```lean
@[simp]
theorem top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v ≠ w :=
  Iff.rfl
```

## completeBipartiteGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, lines 155–157:

```lean
@[simps]
def completeBipartiteGraph (V W : Type*) : SimpleGraph (V ⊕ W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
```

## Fintype.card

`Mathlib/Data/Fintype/Card.lean`, line 40:

```lean
/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card
```
