# Slice D composed certificates

**16 functions / 21 composed occurrences CLOSED. Driver root OPEN; deployed security target not yet established.**

NFQ_CERTIFICATES.json discharges each row using the unchanged NFK materializer, row checks and admission routine. NFQ_certify.py adds source-body, frozen graph/lock, matched-control, complete-result, KMX and ax2 checks. It never edits NFK/NDT or accepts a new trust premise. NFQ_COMPOSED_LEDGER.json.xz preserves all other 566 occurrence statuses.

| Function | Native/control | Model theorem | Rows |
|---|---|---|---|
| `crates/aspis-r1-cost-probe/src/compact.rs::compact_row` | NFQ_K002 / NFQ_K003 | `NFQ_RowShape.compact_reference` | TX1:097 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape` | NFQ_K004 / NFQ_K005 | `NFQ_RowShape.reference` | TX1:153 |
| `crates/aspis-r1-cost-probe/src/transport.rs::Variant::folds` | NFQ_K006 / NFQ_K007 | `NFQ_Transport.folds_reference` | TX1:172, TX2:097 |
| `crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len` | NFQ_K008 / NFQ_K009 | `NFQ_Transport.final_len_reference` | TX1:171, TX2:096 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size` | NFQ_K010 / NFQ_K011 | `NFQ_Transport.checkpoint_size_reference` | TX1:187, TX2:112 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_buffer_meta_ok` | NFQ_K019 / NFQ_K020 | `NFQ_Readonly.reference` | TX1:334, TX2:222 |
| `crates/aspis-core/src/field.rs::M31::neg` | NFQ_K021 / NFQ_K022 | `NFQ_FieldLaws.neg_value` | TX1:018 |
| `crates/aspis-core/src/field.rs::CM31::from_m31` | NFQ_K023 / NFQ_K024 | `NFQ_FieldLaws.cm_reference` | TX1:004 |
| `crates/aspis-core/src/field.rs::QM31::from_cm31` | NFQ_K025 / NFQ_K026 | `NFQ_FieldLaws.qm_reference` | TX1:025, TX2:018 |
| `crates/aspis-core/src/field.rs::M31::reduce_u62` | NFQ_K029 / NFQ_K030 | `NFQ_Reduce.source` | TX1:019 |
| `crates/aspis-core/src/field.rs::PreparedQm31Multiplier::new` | NFQ_K031 / NFQ_K032 | `NFQ_PreparedMultiplier.source` | TX1:023 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::variant_expected_output` | NFQ_K033 / NFQ_K034 | `NFQ_StatementLaws.expected_reference` | TX1:265 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::copy_variant` | NFQ_K035 / NFQ_K036 | `NFQ_StatementLaws.copied_reference` | TX1:238 |
| `crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs` | NFQ_K037 / NFQ_K038 | `NFQ_StatementLaws.limbs_reference` | TX1:310 |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::c0` | NFQ_K054 / NFQ_K055 | `NFQ_WideGetters.c0` | TX2:029 |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::c1` | NFQ_K056 / NFQ_K057 | `NFQ_WideGetters.c1` | TX2:030 |

All credited gates use the actual frozen function and real callee bodies. No credited proof uses stub_verified; separate shape controls cover usize, Option<(u8,usize)>, compiled enum, four-word array and nine-word record. Every native contract has empty modifies, a complete scalar/fixed-array/record or full ProgramResult assertion, and its inverted-ensures control fails on exactly that check. Constructors/getters preserve raw words without narrowing; M31 neg and Prepared construction state canonical input domains; reduce_u62 retains the documented <2^62 precondition. Their consuming callers remain OPEN until those domains are established there.

Prepared construction uses only M31/CM31 additions. NFQ_PreparedMultiplier.source proves the complete nine-word natural spec and derives canonicality for the intermediate CM sum and all three row additions. QM31/WideExact addition edges are resolved as conservative receiver alternatives using the frozen typed body, not treated as actual calls. NFQ_PreparedDomain.output_domain proves all returned words canonical. The reducer executes reduce_u64, whose all-u64 CLOSED Q domain includes this caller bound. Scalar Variant chains execute actual callees with the same full enum domain.

KMX-dependent fixed-value certificates use exactly the shared patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Copy controls: K027/K028 for Prepared9, K039/K040 for array4, K052/K053 for WideExact8/QM31x4. Each positive and wrong-copy negative uses the same stubs, features and bounds as the associated value shape. No custom copy stub was written. No nonlinear field multiplication is proved in Kani.

E001 extracts the five scalar references, and E003 extracts the readonly/scan references with the NCO pins. E002 failed on the first reference extraction shape and earned no credit; E003 follows a changed reference. Existing emitted field/statement definitions and existing record-projection port shapes are reused with new focused value/roundtrip theorems. L048 imports all new statements with the coherent NFN/headline closure. WideExact getters use the existing NBG_GetterPorts projection shape, revalidated against the loaded FIo/CurrentWide records with both complete inverse carrier laws; no new arbitrary port predicate is assumed.

Ax2: L010 is reused for six scalar roots. L050 audits the 36 new roots in five groups; all walks complete, equal collectAxioms, standard axioms only, with eight planted/mutation fixtures in that same newly linked binary. NFQ_STAGE2_DRIVER.diff changes only root/module selection relative to the initial checked runtime. The NEP walker is byte-identical and actual Aeneas/library objects are pinned in each host receipt.

Excluded native successes: cm31_mul_r K050/K051 uses a direct value shape rather than the required field-product opaque call-log form, so it remains OPEN despite its complete Lean theorem. require_zero K058/K059 is one four-byte source-cut result fragment; K060 proves its pointer position but has no matched pointer control. NFQ_ZeroSource.source establishes the full finite-loop model equivalence and NFQ_ZeroStep the general model step, but physical window/frame lift remains OPEN. Neither result appears in NFQ_CLOSED.json.

Each native run validates the frozen resolved graph before launching under CARGO_NET_OFFLINE=true, then confirms Cargo.lock unchanged. Body hashes/ranges are checked directly against frozen 4bb3b3f... and native source snapshots. Verifier/program/statement deployed feature selections and exact rule15 reachability assessment are in NFQ_FEATURE_PARITY.json. Standalone core/statement targets retain the frozen reachable body and required feature closure; unrelated workspace feature unification does not affect these pure helpers. No shipped source changed.

Retained: root carrier/ABI/library/source-to-ELF interpretation; P6/D188 option-A native contract semantic transport is explicitly a reclassification, never removal; RuntimePersistence; accepted RuntimeReturnData/RuntimeMemcmp; runtime digest=H. No headline premise, numerical soundness loss, privacy obligation or two-transaction condition was retired. No claim that CLOSED local/helper rows establish the 100-bit per-attempt target.
