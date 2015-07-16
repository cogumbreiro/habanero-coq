Require Graphs.Core.

Module G := Graphs.Core.

Record Digraph := mk_digraph {
  vertex : Type;
  Edge : (vertex*vertex)%type -> Prop
}.

Notation edge d := ((vertex d) * (vertex d))%type.
Notation walk d := (list (edge d)).
Notation Walk d := (G.Walk (Edge d)).
Notation Cycle d := (G.Cycle (Edge d)).
Notation cycle_def d := (G.cycle_def (vertex d) (Edge d)).

