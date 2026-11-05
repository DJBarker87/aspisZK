# Final caller substitutions and exact domains

No field multiplication is executed or proved in Kani. No new multiplication stub. All oracle/log/counter state is local; no writable static and no function-pointer-dependent assertion.

| Reached child substitution | CLOSED child / paired model law | Caller domain and effects |
|---|---|---|
| EbyKDot::push -> `oracle` / `dot_oracle5` | NGJ CLOSED NFG packet; NGU_LPm_PublicPort.source and NGU_LPm_PointLoop.model_push; NGY_Thread.logged_post | Exact selected coefficient/scalar and full Dot prestate. Canonical coefficient/scalar and count<29 derived from SAME ReadDomain/Bounded and field reply. Native oracle returns both Result<(),()> arms and arbitrary full c0.sums/c1.sums/count poststate; no other mutable object is reachable. |
| weights::field -> `field_oracle` (point5 only) | NGJ Q row TX1:196/TX2:134; NFQ c0; NGY_FieldSpec.source_local/source, NGY_Decoder.selected, NGY_DirectRead.source | SAME live readable y1 length928, lane<29, exact selected32-byte window and eight words<P. Native records actual safe slice's pointer/length/lane and entire E reply, returns arbitrary full E unchanged; no input mutation. Lean substitutes the CLOSED exact field result and derives Dot canonicality. |
| ptr::copy_nonoverlapping / [u8]::copy_from_slice -> KMX originals | Exact evidence/kani-mitig-20261028/KMX_copy_stubs.patch, pin NGY_KMX_PIN.json; existing KMX_CopyMeaning laws / NGY_Window | Source hashes checked before every run. Original NGU_K038 correct and K039/K040 wrong-value controls reused by receipt SHA, same tool/features/patch. Every credited new caller has an argument-corruption control. |

The actual safe borrowed field argument is passed directly from the frozen operand y1. Its identity log is combined with the checked empty external modifies frame; no typed borrow/ownership is manufactured from integer addresses. The full field reply feeds the Dot scalar in the same execution, and order is [field,Dot].

K029 PASS; K030 Dot scalar corruption FAIL; K031 field-lane corruption FAIL. Points0..4 passing/control pairs are in NGY_NATIVE_MATRIX.json. All full-state and both-Result properties hold in each joined caller contract, rather than separate fragments.

The earlier `field_spec` natural-byte stub (K028) timed out, supplies no native credit and is not reached by the final point5 certificate. Its full eight-word Lean law did pass (L010); that law is reused for child installation. No timeout is reclassified as a pass.

Function-contract fidelity: both the plain Out and pointer-log Out5 interfaces pass weak contracts/real bodies, reject inverted/false ensures, reject the unimplied caller assertion under stub_verified, and detect an external Cell write outside modifies(). K032-K043. stub_verified is used ONLY in these deliberately failing fidelity controls; production caller composition uses explicit local logging oracles and CLOSED child bridges. Reviewed native semantic transport remains P6/D188 option-A RECLASSIFICATION.
