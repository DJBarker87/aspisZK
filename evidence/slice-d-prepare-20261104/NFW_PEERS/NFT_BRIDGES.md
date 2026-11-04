# NFT field-helper bridges

**11 functions / 12 new Slice D rows CLOSED under NDT/NFK semantics through unchanged NFQ/NFK validators with stricter additive NFT gates.** Baseline NFQ D21/343 CLOSED becomes D33/343 CLOSED, 310 OPEN. Whole ledger:252 CLOSED,2 QUALIFIED,333 OPEN. The driver remains OPEN; the 100-bit per-attempt target is not yet established.

| Function | New CLOSED rows | Native / matched control | Complete model root |
|---|---|---|---|
| field.rs::CM31::write_le_bytes | TX2:008 | NFT_K006/NFT_K007 | NFT_Bytes.cm_value |
| field.rs::QM31::write_le_bytes | TX2:024 | NFT_K008/NFT_K009 | NFT_Bytes.qm_value |
| field/wide_exact.rs::WideExact::new | TX1:055, TX2:037 | NFT_K012/NFT_K013 | NFT_WideNew.source |
| field.rs::CM31::square | TX1:011 | NFT_K020/NFT_K021 | NFT_Square.source |
| field/wide_exact.rs::WideExact::neg | TX1:054 | NFT_K014/NFT_K015 | NFT_WideNeg.source |
| field.rs::qm31_from_karatsuba_channel_sums | TX1:037 | NFT_K036/NFT_K037 | NFT_Karatsuba.source |
| state_only_hiding.rs::cm31_mul_r | TX1:072 | NFT_K059/NFT_K060 | NFT_Cmr.source |
| r1_pool_adapter_owned.rs::require_zero | TX1:342 | NFT_K048/NFT_K049 | NFT_ZeroJoin.source_and_frame |
| field.rs::qm31_pack_base4 | TX1:039 | NFT_K040/NFT_K041 | NFT_PackWords.source |
| field.rs::qm31_m31_dot | TX1:038 | NFT_K076/NFT_K077 | NFT_DotSource.source |
| field.rs::qm31_sum_products3_prepared | TX1:042 | NFT_K092/NFT_K093 | NFT_PreparedSum3.source |

Every entry has its own caller certificate, same-input child-domain proofs and complete Result/output/frame association. Exact receiver resolution excludes only spurious union-carrier alternatives; every selected internal edge is CLOSED. Details and packet provenance are in NFT_CLOSED.json, NFT_EDGES.json and NFT_CERTIFICATES.json. Each candidate retains frozen body hashes, support hashes and NFK semantic seals. No unrelated status changes are admitted.

The dot row covers the adopted Slice D seven-row internal-pair caller, not arbitrary other callers. Frozen state_only_poseidon.rs:530 constructs ROWS=[2,3,4,5,6,7,8] and maps the same weights/constants before its two calls. K076/077 prove the selected same-window read and term, K063/064 arbitrary-prestate term, K065/066 reducer fold, K070/073 fixed7 control; existing coherent FIq term/outer-loop induction and full7 theorem are reused in NFT_DotSource.source. K069's generic5..80 control timeout is excluded. Generic out-of-D lengths require their own packets.

The prepared3 row composes exact frozen right-cache prefix, native27-cut control, arbitrary-prestate selected product cell and all-other-cell frame with the actual emitted runStep and loop induction. PreparedFor and the CLOSED constructor's output-domain law establish canonical cache words. The final converter is newly CLOSED here. The generic accumulation helper and small2/3/4 path remain OPEN; this prepared function does not call them.

require_zero now has the matched pointer control missing from NFQ. Native arbitrary windows in completely arbitrary4096-byte backing prove pointer, Result/tag, length and immutable frame separately. Symbolic padding/suffix laws preserve the same allocation/input at every index; NFT_ZeroJoin.source_and_frame joins these to NFQ's finite-loop source theorem. The actual owned caller checks S2 checkpoint_size=1768 before borrowing and invokes require_zero on that same checkpoint view. The approved SDK same-view law remains explicit trust.

Field products use local opaque call logs and named Lean value laws in LPh_STUBS.md; no variable field product was proved by Kani. KMX is exactly the prescribed bcdf749b… patch, with shape-matched failing copy controls in the same source/configuration. No writable static, callback/function-pointer quarantine credit, or stub_verified is used in these new packets. Byte writers use complete value and disjoint arbitrary-prestate guard-window frame proofs; short packer uses explicit zero initializer, generic prefix law, full padded graph and all4 raw coordinate laws.

E002/E003 safe references use NCO extraction pins and unchanged generated outputs. L021 audits the initial12 roots; L060 audits58 additional roots using the byte-identical NEP walker. Both binaries pass all8 planted/mutation controls. Raw walks equal collectAxioms, with only propext/Classical.choice/Quot.sound. L058 imports the coherent deployed headline and prints standard axioms. Per-target exact exit/wall/RSS/swap/revision/axioms are in NFT_RESULTS.json and original receipts. No unchanged full regression was repeated.

NFT_certify.py checks the hash-pinned NFQ composed baseline and invokes unchanged NFK certificate_checks/materialize_recipe/row_checks/admit. It adds frozen-lock/offline/source/features, exact KMX/matched controls, all copied source/config pairs, source erasure, current successful model-source hashes, raw graph hashes/axioms and same-call child-domain gates. NFT_TESTS.json records72 recipe mutations; supplemental validator mutations are separate. NFQ and NFK source hashes are recorded, not rewritten.

Trust is retained/reclassified: P6/D188 NativeContractSemanticTransport optionA, root physical carriers/ABI/unique borrows, compiler/library/Aeneas/source-to-ELF and SDK view transport; RuntimePersistence, RuntimeReturnData and RuntimeMemcmp remain accepted runtime rows, and runtime digest=H realization remains explicit. L154 remains a statement parameter, D188 narrowed, headline AspisR1.RPx_Deployed.deployed. No premise retired, no security/privacy/two-transaction metric change.

All100 Kani,60 Lean/support,3 extraction slots are used. K005/K069 timeouts and K056 pre-CBMC compiler failure earn no credit; E001/L009 and L015 native-axiom draft are excluded. No cap/timeout increase or unchanged timeout rerun. Own scratch changes are supplied in NFT_HARNESSES.patch, with per-attempt pinned snapshots. Repository crates/programs and all shipped files remain unchanged; inherited ELF pins remain applicable. No key action, deployment, push or other worker edit.
