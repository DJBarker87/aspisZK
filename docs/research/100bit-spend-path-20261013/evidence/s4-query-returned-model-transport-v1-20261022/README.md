# S4 returned callback values to recovered-word model

This focused Lean result keeps the exact callback witness and its four returned values. Given packed maps whose selected leaf stores the exact raw opening prefix and suffix, it transports those values to the recovered-word first-fold model. The packed-map premise stays conditional inside the same existential witness.

It does not prove packed-map authentication or that the recovered leaf equals the query's source cast index. Those bindings remain upstream.

The theorem is `AspisR1S4QueryReturnedModelV1.returned_local_batches_model_transport` in `sources/S4QueryReturnedModelV1.lean`. Its direct proof dependencies and source/object pins are recorded in `manifest.json`; the Lean object is intentionally omitted.

Verification used Lean 4.32.0, `-j1 -M 4400`, with the exact selected `LEAN_PATH` captured in `evidence/LEAN_PATH.txt`. The recorded run exited 0 in 37.795 seconds, peak aggregate RSS 3,939,090,432 bytes, peak process RSS 3,941,728,256 bytes, and zero swap. `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`.
