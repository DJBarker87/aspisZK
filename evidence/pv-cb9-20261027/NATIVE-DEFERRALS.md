# Native effect handoff to pv-runjoin

No callback row is discharged by this handoff. The listed cb9 roots have value/control extraction obligations, retained here. Separate effects require real RunJoin proofs:

| Native effect | Relevant ops | Exact reason deferred to pv-runjoin |
|---|---|---|
| Vec capacity, reserve, allocation/OOM and ownership | 226, 228, 251 | Complete observable Result and failure event require the concrete allocator/runtime, not a pure vector value or omitted error path. |
| Box allocation and owner lifetime | 252 | Weights::new returns an owned Box; value extraction alone does not prove allocation/failure/Drop effects. |
| OS entropy and failure/public signal | none of the listed pure roots | The capped trust interface remains exactly entropy_law, entropy_kernel, observation. No new trust field. Witness independence of the public failure event remains a P obligation. |

The loan-validation/structured-Drop refusals are extractor outcomes; they are not evidence of a native effect law and do not discharge any row. No native-effect callback is replaced by a total value function. No key or wallet touched.
