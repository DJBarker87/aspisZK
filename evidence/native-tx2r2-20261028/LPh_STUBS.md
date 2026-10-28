# NCN substitutions and domains

All Rust changes are scratch-only patches over frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
No repository crate/program changed. No multiplication body is proved in Kani.

| Stub/contract | Paired checked fact | Domain and admission |
|---|---|---|
| KMX ptr copy / u8 slice copy, `NCI_kmx::KMX_*` | Exact official `evidence/kani-mitig-20261028/KMX_copy_stubs.patch`, SHA256 `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`; inherited KMX_CopyMeaning value laws and NCI_KMXFrames | Exact verbatim implementation. Each credited copy-dependent window has its matching failing control; full1768 source windows and valid64-row allocations as specified in bridge tables. No own copy stub. |
| `residue_limb_at` / `power_limb_at`, stub_verified | Actual proof_for_contract K010/K012, inverted controls K011/K013; model `NCI_GetterModel.array_get` audited L024 | Arbitrary four-U64/four-U32 record, index<4. Exact selected scalar, readonly. Product caller K014 timed out and is excluded. |
| `Reader::k`, stub_verified weak Result contract | K022 actual full1768 cursor proof; K020 inverted ensures, K021 modifies violation, K023 real is_ok and K025 unimplied-under-stub failure; caller K026/K027 | bytes.len=1768, at<=1752; modifies only cursor, advances16 on either Result. No byte/decoding/canonical-output equation is promised by this weak contract. Weights prove at=712+16*i, i<64; semantic helper proves408+16*i, i<10. Exact replies are selected through the imported raw/codec lower bridge, never assumed independently. |
| `NCN_vec::row`, stub_verified pure record contract | K059 actual Vec index contract, K060 inverted control; actual value caller K061/K062; generic model index law and `S8Kani2MutableValue.value_eq_entry/valueAt_success` imported through NCI | Valid64-row Vec, index<64; returns exactly raw[index], readonly. This does not supply fallible allocation, arbitrary runtime heap admission or parent dictionary installation. |
| `NCN_u10::reduce` / `NCN_vec::reduce` replacing M31::reduce_u64 | `AspisR1.NCI_PendingReducer.reducer_ok` and `primitive_eq`, freshly audited L024 | EVERY U64. any U32 constrained to x mod2147483647, with actual emitted ok/value/canonicality supplied by the named theorem. Actual value passes the SAME row limbs; no nonlinear field-product assumption. |
| Inherited opaque multiplication log, NCI_steps::mul | `AspisR1.NCI_FieldLog.instantiate`, Realized, LPf_BaseMultiply.source, audited L024 | Native basis/node windows establish canonical inputs and log exact operands and arbitrary canonical reply; Lean chooses emitted product reply. Unchanged NCI scope only; no new multiplication caller gate is claimed. |
| `NCN_slices::weak`, borrowed slice-returning shape | K048/K049/K050/K051, but K052 cannot codegen `&[u8]: Arbitrary` | NOT ADMITTED for call-site substitution. No dependent caller used it. No foreign-ref fabricator or pointer-word carrier is introduced. |
| `contains_never<T:PartialEq>` unreachable sentinel | K077 checks the sentinel unreachable on q>=262144; `NCN_QueryDecision.reject_at` with empty pre proves matching model guard | NO NATIVE CREDIT: missing matching negative after budget exhaustion. Promises no semantics for any reached contains call; cannot be used for in-range/duplicate cases. K076 nongeneric signature codegen failure is retained. |

The concrete Request backend in K070–K075 logs exact proof/public/checksum input
slices and returns arbitrary selected replies at the header/hash prefix. It is
neither a SHA implementation nor the actual SolanaDigest forwarding bridge.
Digest VALUE stays the existing runtime realization; U00 forwarding and actual
fixed-input provenance stay open. The prefix is a source-pinned cut, not an
accepted full resume. Reply mismatch coverage is `NCN_MismatchWitness.mismatch_witness`.

Native integer multiplication gates K014/K028 timed out and have zero credit.
The checked MODEL product/add is `NCN_ModelStep.product_write` reusing
NCI_ResidueWords; model cadence is `NCN_Cadence.flush`; checked MODEL one-fold
mask/shift/add is `NCN_FoldWord.source_ok`. These are not surrogate native passes.
