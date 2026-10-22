# S4 Fin 26 head codec wrapper

`AspisR1S4HeadCodecProjectionV2.c1_m31_head_term_fin26` lifts the single-term codec theorem to all 26 C1 head coordinates. It accepts the same-opening byte identity and one pointwise same-g power theorem over the 29-element `g` vector, derives each selected array-cell witness internally, and concludes the pointwise head equation expected by the width-29 fold theorem.

The focused Lean check is green under Lean 4.32.0, with one thread and `-M4400`; it reports only standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The imported head codec module is pinned to the source/object recorded in the prior source-only packet. No compiled objects are included.
