# PCB stubs and retained trust

No field multiplication is proved in Kani. No field multiplication stub is used by an accepted PCB packet. No new runtime value law, function-pointer/Option<fn> credit, or mutable-static oracle is adopted. P6/D188 native semantic transport is an option-A **reclassification**, never trust removal.

| Native replacement | Paired Lean/source law | Domain and status |
|---|---|---|
| `PCB_178::correct` for `as_tree` | `PCB_GetterLaws.tree`; literal frozen identity and wrong-place mutations in PCB_GETTER_IDENTITIES.json | All valid live immutable receivers, same loan and `receiver.inner`; y-prime correct/wrong-place controls067/058. Accepted178; dependent176 uses same receiver and059/060. No borrowed `stub_verified`. |
| `PCB_291::correct` for `seed` | `PCB_GetterLaws.seed`; same source identity record | All live immutable plans, same `receiver.seed` loan;061/062. Accepted291. |
| `PCB_343::correct` for terminal `Deref` | `PCB_GetterLaws.value`, specialized to the actual canonical terminal result carrier | Same boxed pointee/loan;063/064, source identity, no allocation replacement. Accepted343. |
| `PCB_355::correct` for canonical-state `Deref` | `PCB_GetterLaws.state` | Same boxed state and loan;065/066. Accepted355. |
| Exact KMX slice/pointer copy stubs | `KMX_CopyMeaning.loop_spec`, `copy_frame`; `NCI_KMXFrames`; PCB_AppendFrame laws | Only the outlined32-byte append window and2-byte count window.033/034,035/036,053/054. This is partial279 evidence, not whole-page credit. |
| `PCB_344::clear_empty` for SDK `set_return_data` | Candidate `PCB_FinalLaws.clear` + extracted unit012 + exact source request/covered native oracle | Exact empty request and unique unit reply.070 PASS/071 wrong request FAIL; unit-shape115–119 fidelity controls pass expected verdicts. Existing RuntimeReturnDataClear effect trust retained. **OPEN candidate** because aggregate060 fails at290. |
| `PCB_184::encoder_reply` | Prepared flat encoder assumption; association to CLOSED shared encoder bytes is still OPEN | Unrun, unused, no credit. Never treat this prepared stub as discharged. |

Wrong-place/wrong-request replacements are failing controls only. They are never accepted callee laws. Existing unrelated frozen cfg(kani) mutable-static warnings do not confer credit and are not used as selected-harness oracles.

KMX patch SHA256: `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`. PCB_gate.py checks all three exact KMX inputs before every native run; no copy stub was modified or invented. Relevant native harnesses use the exact KMX stubs and matched negative controls. The selected-field owned-tree observation107/108 receives **no copy-dependent native bridge credit**.

PDA replies remain quantified op38. Coherent digest/error slots remain op43/op44. SHA realization remains RuntimeSha256Value; return-data values remain RuntimeReturnData (nonempty1..1024), and clear remains RuntimeReturnDataClear. No SHA/PDA implementation was unwound. CLOSED NLG callees must be consumed at SAME arguments with proved clauses; no XRn join/stand-in or shared-row re-ownership is used.
