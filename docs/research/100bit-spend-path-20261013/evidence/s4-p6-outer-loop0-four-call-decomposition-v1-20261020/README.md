# S4 P6 four-call loop0 decomposition

This source-only packet strengthens the same-closure N=4 trace. From one successful composed N=4 P6-model array call, it derives callback successes for the same `(q,g)` at slots 0–3. Each successful callback is further decomposed into the exact generated `step_by` initialization, its successful generated `call_mut_loop0` execution from the zero limb array, and the matching N=8 P6 array call.

The proof keeps the operation record and source loop call explicit. It does not yet apply the existing seven-batch bound to these loop outputs; reconciling the loop's exact `FourDotsOps` owner with that bound is open. Rust `array::from_fn` correspondence and full S4 caller closure are also open. Parent sources and object pins are enumerated in the preflight and manifest.
