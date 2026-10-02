# R419 comparator hardening delta

The initial draft is preserved as `compare_llbc.initial-draft.py`; the reviewed general draft remains `compare_llbc.py`. The stricter implementation is separate in `compare_llbc_hardened.py` so the original audit artifact is not overwritten.

The hardened draft fails closed on cyclic `HashConsedValue`/`Deduplicated` references (it raises instead of emitting a cycle marker), malformed wrapper shapes/payloads, unresolved references, duplicate edit paths, empty/root replacement paths, and ancestor/descendant or duplicate path overlap. It also requires exact edit object keys, a fully specified expected post-deletion list for a list-item drop, and exact before values. It still performs no transformation of an LLBC file; the permitted operations apply only to an in-memory copy for comparison.

`test_hardening.py` exercises seven tiny synthetic cases: cycle rejection, two malformed wrapper rejections, root replacement rejection, ancestor overlap rejection, incomplete list-drop rejection, and a positive exact-leaf operation showing a sibling executable field remains unchanged. Receipt: `synthetic-negative-cases.json`. These tests validate guard behavior only, not admissibility of any R419 edit or correspondence to source.

No candidate LLBC or approved edit manifest was supplied. The original R396 baseline and R418 census remain unchanged. No Charon/Aeneas/Lean or package build was run.
