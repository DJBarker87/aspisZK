# Lean-discharged powers products

| Native cut/oracle | Paired Lean theorem | Domain and call-site discharge |
| --- | --- | --- |
| NFW_weights::product(local log,left,right), opaque canonical reply | AspisR1.NFW_LPi_TowerValues.wide_mul | Every eight-word operand limb<P. The native generator admits all canonical E; NFW_LPi_PowersSource.one_canonical and NFW_LPi_PowersValue.loop establish canonicality of every next operand. The returned value is substituted by the natural-number mulE specification and canonical output given by wide_mul. |

The oracle records exact same operands and returns an unconstrained canonical record; it does not evaluate multiplication in Kani. It is an opaque call-log cut under ruling(y), not a proof_for_contract or stub_verified claim. The model theorem returns ok with exactly mulE on the domain. K005/K007 prove operand order and caller frame; K006/K008 are matched failing controls. Source fields/pointers and complete effects remain in the root interpretation boundary. Final-iteration proof NFW_PowersFrame.final requires no product domain, because no product call occurs.

## Constructor cuts (partial; not composed credit)

| Local cut | Paired model/callee theorem | Required caller domain / status |
|---|---|---|
| `NFW_prepared::power(gamma, ops)` | `AspisR1.NFW_PowersCohort.source`; same-input port `NFW_SampledDomains.same_gamma` (pending its focused audit) | Eight canonical gamma limbs, N29. `NFW_SampledDomains.prepared_gamma` derives this from the same adopted producer; native scalar association still OPEN. |
| `NFW_prepared::claim(sem,y1,inactive,g,kappa,ops)` | CLOSED LPt_/KNF_ prepared_claim static-form packet, named by NFQ_REMAINING; installation OPEN | Same verified semantic rows, y1 width928, canonical inactive/kappa/g and source claim payload. Native argument association alone is insufficient: complete semantic/claim domain and exact callee theorem installation remain OPEN. |
| `OracleTranscript::{new,scalar,queries,scalar_k}` | `NFW_Transcript.{seed,absorb,block}` plus canonical sampler laws; constructor model `NFW_PreparedControl.source` | These are typed local-record cuts, not field arithmetic stubs and not admitted child packets yet. Exact state, rows, payload bytes/modes and Result errors are checked separately. Runtime syscall bytes/reply association remains OPEN. |

The constructor cuts do not execute field multiplication in Kani. Arbitrary
canonical replies do not by themselves discharge a callee's semantics. No
unpaired claim cut is reported as a CLOSED bridge. The semantic fixture is an
overapproximation of Rust storage, and is not evidence that claim's semantic
producer domain has been proved.
