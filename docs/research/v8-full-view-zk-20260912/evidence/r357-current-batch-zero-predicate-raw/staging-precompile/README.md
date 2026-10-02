# R357 batch zero-predicate raw fragment

Mechanical, uncompiled staging of six exact declarations from the frozen R292 translation: the batch closure's `Unit` type row, `B.PartialEq::eq`, `call_mut`, `call_once`, and the `FnOnce` and `FnMut` implementation values. The exact frozen source files and individual byte excerpts are under `provenance/`; `build_raw.py` reproduces the target file and `source/R357BatchZeroPredicateRaw.lean` byte-for-byte.

The adapter imports `AspisR249R110Raw` for the existing `B` representation and `AspisR278PrivateInverseRaw` for `B.ZERO`. It locally copies the source `eq` declaration and the closure callback declarations in one namespace so the copied callback references resolve to the copied qualified name. No replacement, theorem, source correspondence claim, standard-library correspondence claim, whole-batch proof, compile, promotion, stage, or commit is included. Six `#print axioms` commands are present for lead review.
