# Exact remaining A2 obligations

1. CLOSED: SAME-query full Result geometry equality, NNU_Geometry.source / returned (L015).
2. CLOSED: installed query-loop association, NNU_Query.source / returned (L029), using NNH_Run5bQueryDomain.initial and SAME powers.
3. SAME-resume Merkle parent OPEN; installed-slot and query-domain laws CLOSED (NNU_MerkleSlots, L031); local node/leaf digest laws CLOSED (NNU_MerkleDigest, L038).
4. Offsets CLOSED (NNU_Offsets, L037); source-ordered common converse OPEN.
5. NNH_ExactRemainingTypes.tx2Op11.
6. Stage2To064, op44/op53, Returns, AMN.viaReturns2 at corrected S_host.

No final field or ledger credit is claimed.

## Merkle boundary after installed-slot inspection

`NNU_MerkleSlots.installed` (L031) fixes the installed op5 to Port4B_Install.batch through Op5T_Concrete.stage_source. `same_resume` derives canonical query bounds at the identical returned Prepared. The remaining exact statement is:

```lean
∀ m env err r pub proof ck p a folded,
  NJJ_Common.resume (LIBB_Tx2Reservation.reservation env) (LIBB_PartitionEnv.digest env)
    ck proof pub .S2 () = .ok (.Ok (p,a)) →
  NLP_NativeMerkle.action (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
    proof p folded 1#usize () = .ok (.Ok ()) →
  Port4B_Install.batch
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk m env err r))
    proof p folded 1#usize () = .ok (.Ok ())
```

This is the unproved parent bridge, not an added top premise. Caller proof/checkpoint extents and SAME-resume facts may be derived at tx2Op11; they must not be strengthened. The printed MultiproofConeP6Verify.verifyState_eq requires a total all-partitions digest law and physical length ≤5504. Neither is established at this caller (the binary child packets admit ≤9216); no use or credit is taken from that stronger-domain theorem. Local node/leaf partition laws do not imply the all-input law. The correct route is pointwise native batch/child composition on actual reached node/leaf requests.

## Exact next common and top obligations

The original `AspisR1.NNH_Tx2OpenSlots.inactive` is also still open inside the common converse: `∀ bs : Slice U8, Port1_LibrarySource.decode bs = NJC_ClosedCalls.inactive bs`. No parser/buffer reduction is performed here.

After the Merkle parent and inactive slot, invert the successful `LIBB_Tx2EnvCode.common` in source order and construct the successful `VTop_Stages.verifier.candidate.tx2_common` at `NNH_Tx2SlotTransport.stage m env err r`, with the SDK digest at the SAME arguments. Use NNU_Geometry.source, NNU_Query.source, NNU_Offsets, NNH_Run5bFinishEdge.selected, and the existing SAME-resume/pending/flush/mark ports; derive every local domain from that occurrence. No theorem carrying the entire common equality as a premise is delivered.

Step 5 remains exactly `NNH_ExactRemainingTypes.tx2Op11` (its full definition is in the merged NNH module and remains unchanged). It includes the admitted reservation equality and original Dom064, and concludes the ACTUAL installed SDK op11 reply is `.ok (.Ok ())`. No such constant is delivered here.

Step 6 remains exactly `RSL.TAS.NND_A2 (AspisR1.NNH_Run5bHost.S_host L0 copy std) NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0`: use Stage2To064 at SAME derived cuts, the completed emission tail, NNH_ReturnsBundle.tx2_returns / the guarded returned evaluator, EnvRep at the corrected literal host and AMN.viaReturns2. No Root0, Realizes, success, representation or selector premise may be added to that top.

All remaining obligations are Lean-only. No member requires new Kani or extraction. The stop is the 40-scope job budget; no ledger row or A2 field is claimed.

The independent Stage2 tail/returned-cut draft failed namespace resolution at L039; it is uncompiled/uncredited in NNU_Stage2Tail.lean.txt, with exact errors retained. Restate it at an explicitly qualified adapter owner and compile it alone before integrating. No claim that its contents pass is made. The existing NNH_Stage2To064.source and Returns bundle remain unchanged/read-only; NNU supplies no new successful Stage2 or AMN.viaReturns2 application.
