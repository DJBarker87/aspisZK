# R599 canonical field tuple

R599 proves the deterministic representation bridge between a four-coordinate tuple of canonical sampler values and the exact mathematical QM31 field. It constructs an equivalence `(Fin 4 → Fin P) ≃ QM31Exact`, proves that the sampler list decoder agrees with the forward map, and proves that any length-four list whose entries are all below `P` decodes to a tuple field value exactly when the list is that tuple’s ordered canonical limb list. Here `P = 2,147,483,647`.

The theorem source is [R599CanonicalFieldTuple.lean](lean/AspisV8R19/R599CanonicalFieldTuple.lean), SHA256 `eb4d5dfb9c8bc42f5a0086ff203291a592d7f67bc01990de489862fb4dc242a5`; source revision `cf76c5592e12afd36da0ad4a432b4626dc5f02f7`. The equivalence is implemented from the four `QuadraticAlgebra` coordinates and the existing `ZMod` natural-value representation. The proof establishes all four coordinates, including zero values; there is no nonzero-value restriction.

The final focused check compiled the canonical module path with Lean `-j1 -M4500` in the pinned cached workspace, under `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. Attempt `1791091013969211000` exited 0 in 1.47 seconds, with peak Lean-child RSS 3,269,136 KiB and swap 0. Complete axiom output:

```text
'AspisV8R19.R599CanonicalFieldTuple.tupleFieldEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R599CanonicalFieldTuple.tupleFieldEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R599CanonicalFieldTuple.ofFn_four_values' depends on axioms: [propext, Quot.sound]
'AspisV8R19.R599CanonicalFieldTuple.listDecode_tuple' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R599CanonicalFieldTuple.decode_eq_tuple_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All five attempts, exact source snapshots, logs, and receipts are retained under [evidence/r599-canonical-field-tuple](evidence/r599-canonical-field-tuple/). The first three attempts preserved proof errors; the fourth succeeded with linter warnings; the fifth removed those unused simp arguments and is the clean final check. No check was rerun unchanged.

This is only a deterministic representation result. It does not prove that the actual source sampler’s output has this distribution, that its adaptive retry process realizes the finite-tuple law, or that accepted circle outputs follow a uniform law. Those probability and source-correspondence obligations remain open.
