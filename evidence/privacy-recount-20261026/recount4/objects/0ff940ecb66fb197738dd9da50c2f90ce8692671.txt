# Focused direct proof plan

The source `records` body itself has no structured Drop. The first failing bodies are generated FnOnce adapters for the two public `from_fn` closures and the `raw` closure, plus generic drop glue. They are not a reason to erase a destructor.

Precise drop elaboration + desugaring + monomorphization produces zero structured Drop nodes. Aeneas then fails while resolving a trait method (core/ops/function.rs:250). `--translate-all-methods` produces byte-identical declaration data, so its translation is not repeated. Next: keep precise/desugared drops but retain normal Aeneas generics.

If a closed direct source emission succeeds, install only new PV_RunJoin_ modules. Resolve the opaque zero-argument pair_empty_roots callback to the already extracted source-port function at E_shipped with field-preserving adapters. Do not unfold its 21 hashes when proving the mapper equation. Factor both records computations over the SAME Result-valued root helper, prove the continuation equality, and use concrete 24-row/8-lane fixture arrays first. No source dictionary equality is assumed. Generic arguments are attempted only after the fixture equations.

If direct emission remains unsupported, the owned extraction is reused. Its nominal call equation is only a reference equation until the unstubbed shipped/reference gate succeeds; naming it R_shipped cannot discharge that gate. All subsequent compiler-return, transition, deployed public-binding, and non-vacuity work remains gated on genuine identification.
