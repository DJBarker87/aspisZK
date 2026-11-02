# NEL slice S composition

**22/97 composed rows CLOSED, up from 14; 0/7 roots CLOSED. Target not yet established.**

Frozen Rust `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; adopted headline `AspisR1.RPx_Deployed.deployed`, coherent SInt2 objects. P6/D188 option A is reclassification, not removal. L154 remains a statement parameter; approved runtime trust, RuntimePersistence, privacy, two transactions and 100-bit PER-ATTEMPT soundness are unchanged.

| Root | Root rows CLOSED | Rows CLOSED in effective subtree |
|---|---:|---:|
| `decode_public_statement_box` | 0/1 | 22/80 |
| `validate_pool_v1_pair_forest_terminal_statement_v1` | 0/2 | 22/50 |
| `encode_pool_v1_pair_forest_terminal_statement_v1` | 0/1 | 22/55 |
| `reconstruct_asq8_statement` | 0/1 | 22/54 |
| `decode_pool_v1_pair_forest_terminal_request_v1` | 0/1 | 14/35 |
| `scan_proof_buffer` | 0/1 | 4/25 |
| `emit_result` | 0/1 | 22/60 |

Subtrees overlap; counts are not additive. Each of the seven native root theorem statements is **not established**: there is no native root theorem or native-root axiom result to report. The complete per-member reasons and remaining hypotheses are in NEL_STOP_AUDIT.json. Only the first root was attempted; the other six remain behind its binding order.

New closed members, in TX1 and TX2: common getter, validate_common, validate private transfer, validate withdrawal. All original non-composition source/native/trust fields remain unchanged. One additional conservative WideExact edge is resolved by its actual M31 receiver; this does not promote the parent loop.

## Imported model root and explicit open laws

The following is the unchanged **model** theorem, not a new native-root result. Its three child instances remain explicit:

```lean
theorem result_and_effects (pay : Pay) (lane : Lane) (late : Late) (s : Statement)
    (payment_bridge : ∀ a, Call.payment a ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      pay a = NED_ValidatorTrace.payment a)
    (output_lane_bridge : ∀ d, Call.lane d ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      lane d = NBN_FirstByteDependency.lane enc d)
    (late_bridge : ∀ a out, Call.late a out ∈ (NEE_ValidatorOracle.run pay lane late s).2 →
      ignore (late a out) = ignore (NBN_LateSummary.run enc a out)) :
    NEE_ValidatorOracle.run pay lane late s =
      (pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s,
       (NED_ValidatorTrace.run s).2)
```

`#print axioms NEE_ReachedRootModel.result_and_effects`: `[propext, Classical.choice, Quot.sound]`, re-audited in NEL_L017. Actual full payment/output-lane/late bridges are not inferred from these model laws.

## Checked support and limits

NEL_L017 audits all 27 new top theorems and the reused root result: exit 0, wall 5.038188611972146 seconds, peak 5,278,844 KiB, swap 0; only subsets of the three standard axioms. The same receipt prints the complete elaborated reached-argument and root statements. Every new theorem statement/source/audit is pinned in the successful focused receipts.

K037 (combined transfer argument/control) and K054 (combined frontier iterator/write) timed out and are excluded. Neither reran unchanged. Replacements split scalar Result/order from immutable fields, and iterator from byte write. K036 own missing Arbitrary trait, K001/K004/K005 compilation errors, and L008/L010/L014 Lean errors are excluded. The common-validator inverted-property control gap was corrected openly in NEL_CONTROL_CORRECTION.md; K060 now corrupts the actual reply and fails with the original expected property.

K058/059 check six independent guarded cases: actual output-lane and first-byte corrupt replies, three wrong borrowed fields, and a corrupt byte update. All six intended checks fail. Result<Unit,PaymentError> and Result<u8,AccountError> fidelity controls detect inverted ensures, uninferred assertions under stub_verified and modifies violations. No writable static or Option<fn>-dependent credit is used.

KMX patch sha256: `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`. Native byte steps are the pinned indexed value operation, never replacement copy stubs. No field multiplication, SHA, whole-buffer protocol-loop proof or unoptimized arithmetic gate was run.

No frozen manifest/release replay ran: native roots remain incomplete. Shipped crates/programs are unchanged; no ELF rebuild trigger fired. Release hashes are inherited pins, not fresh results: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No wallet/key operations occurred.
