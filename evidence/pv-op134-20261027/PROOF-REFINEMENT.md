# Row reference proof refinement

50100: broad simplification of the 214-push reference bridge hit recursion
limit in 2.82 s (2,678,244 KiB, zero swaps). It was replaced by 16-push
continuations; no recursion/heartbeat option was changed.

50102: each of the fourteen segment equalities checked, but the unbroken
source rfl still hit recursion depth, and the full run's rewrite proof hit
Lean's -M7000 kernel memory exception (65.42 s, 7,168,680 KiB, zero swaps).
This is a failed proof attempt, not a counterexample to the ROW. The old
source is retained in 50102-source.lean.txt and the exact errors/axiom output
are retained in out-50102.log. Its declarations are not accepted evidence.

Replacement: split source equality through fourteen prefix-congruence steps,
keeping continuations abstract. Compose segment run equations with named
bind_ok/Equality.trans facts instead of using a rewriting tactic that can
normalize the remaining concrete suffix. The frozen PV_CBM_RowsRaw source,
all PV_CBM statements, and all resource limits remain unchanged. Pending
receipts decide whether this replacement is accepted; no larger-cap retry.

50105: the prefix-congruence source proof checked with standard axioms;
remaining errors were trailing tactics after solved goals and the unfinished
bind_ok reduction (13.57 s, 2,993,096 KiB, zero swaps). Fixed those tactics;
no mathematical statement or cap changed.

50106: replacement accepted, exit 0, 13.53 s, 3,019,216 KiB, zero swaps.
Source, all fourteen segments, generic bind facts, arbitrary-output run under
capacity, and complete Result callback all print standard axioms only.
The former memory-heavy proof is permanently replaced in generate_row_spec.py.
