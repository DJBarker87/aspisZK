# Exact remaining A2 obligations

1. CLOSED: SAME-query full Result geometry equality, NNU_Geometry.source / returned (L015).
2. CLOSED: installed query-loop association, NNU_Query.source / returned (L029), using NNH_Run5bQueryDomain.initial and SAME powers.
3. SAME-resume Merkle parent OPEN; installed-slot and query-domain laws CLOSED (NNU_MerkleSlots, L031); local node/leaf digest laws CLOSED (NNU_MerkleDigest, L038).
4. Offsets CLOSED (NNU_Offsets, L037); inactive CLOSED (NNU_Inactive, L052); source-ordered common converse OPEN.
5. NNH_ExactRemainingTypes.tx2Op11.
6. SAME Stage2 packet/segment/continuation/emission tail CLOSED (NNU_Stage2Tail, L061); op11-dependent Returns/AMN.viaReturns2 and corrected S_host field OPEN.

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

The original `AspisR1.NNH_Tx2OpenSlots.inactive` is now CLOSED by `NNU_Inactive.source / returned` (L052): `∀ bs : Slice U8, Port1_LibrarySource.decode bs = NJC_ClosedCalls.inactive bs`. The structural Result/Option mapping proof evaluates no parser buffer or byte read.

After the Merkle parent and inactive slot, invert the successful `LIBB_Tx2EnvCode.common` in source order and construct the successful `VTop_Stages.verifier.candidate.tx2_common` at `NNH_Tx2SlotTransport.stage m env err r`, with the SDK digest at the SAME arguments. Use NNU_Geometry.source, NNU_Query.source, NNU_Offsets, NNH_Run5bFinishEdge.selected, and the existing SAME-resume/pending/flush/mark ports; derive every local domain from that occurrence. No theorem carrying the entire common equality as a premise is delivered.

Step 5 remains exactly `NNH_ExactRemainingTypes.tx2Op11` (its full definition is in the merged NNH module and remains unchanged). It includes the admitted reservation equality and original Dom064, and concludes the ACTUAL installed SDK op11 reply is `.ok (.Ok ())`. No such constant is delivered here.

Step 6 remains exactly `RSL.TAS.NND_A2 (AspisR1.NNH_Run5bHost.S_host L0 copy std) NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0`: use Stage2To064 at SAME derived cuts, the completed emission tail, NNH_ReturnsBundle.tx2_returns / the guarded returned evaluator, EnvRep at the corrected literal host and AMN.viaReturns2. No Root0, Realizes, success, representation or selector premise may be added to that top.

All remaining obligations are Lean-only. No member requires new Kani or extraction. The stop is the 40-scope job budget; no ledger row or A2 field is claimed.

The original namespace-failed Stage2 draft remains archived. Its corrected,
explicitly qualified version `NNU_Stage2Tail.lean` compiles ALONE at L061.
`emitPacket`, `tail`, and `returnedCuts` have standard axioms only. In particular,
returnedCuts derives the SAME packet, segment, original Dom064, successful
LIBB code, native continuation equation and emit success from the returned
reference. This does not establish the missing actual SDK op11 reply.

## Continuation frontier after L041–L080

All remaining members are Lean-only. None needs Kani or extraction. The stop is
the separately authorized 40-scope continuation budget, not Kani exhaustion.
No final field, type-equality example, raw ax2 NND_A2 audit or ledger credit exists.

3. The exact parent statement above is still OPEN. New checked components:
   NNU_MerkleLeaf/Node/Levels/Environment, MerkleValidity/Head/Root/Wrapper,
   MerkleEndpoint.selected, MerkleVerify.selected/sdk, MerkleNative.batch,
   MerkleChildren, MerkleCount.source, MerkleOpening.source,
   MerkleIteration.source and MerkleKeys.source. They use pointwise node/leaf
   digest laws and SAME resume domains, without global repartition invariance
   or the unjustified 5504-byte bound. The active iteration is one actual native
   iteration on arbitrary scratch with its stated invariant/observations.
   Still required: reconstruct the successful terminal iteration using the
   same count/slot/padding/verify reads; propagate KeyStream, position, room and
   opening bounds through the native loop; compose tree0,tree1,tree2 with exact
   returned arrays. L076/L077's installed-count rewrite shape is retired.
   The isolated L078 frame draft fails only its implicit polymorphic op10
   projection header; it has no accepted object. Its explicit-H projection
   repair must be compiled separately before terminal construction.
4b. Inactive is CLOSED. NNU_CommonCuts.source extracts source-ordered local
   witnesses; NNU_CommonResume.occurrence derives canonical fields/next at that
   SAME deterministic resume; NNU_CommonSelected.source constructs the installed
   geometry/query replies at the SAME powers/pending witness. Still required:
   construct the entire candidate.tx2_common continuation in source order,
   including Merkle, all ranges, pending/flush/mark and the selected finish edge.
   No theorem assumes the whole common equality. No common converse is claimed.
5. NNH_ExactRemainingTypes.tx2Op11 remains OPEN exactly as defined. It needs the
   original reservation equality/Dom064 and actual installed SDK op11 success;
   local source observations do not replace the enclosing common/parser port.
6. The exact corrected-host RSL.TAS.NND_A2 remains OPEN. The independent SAME-cut
   Stage2/emission work is done; the actual op11 reply is needed before applying
   the continuation, Returns/guarded returned evaluator, corrected-host EnvRep
   and AMN.viaReturns2. No Root0, success, representation, selector, Realizes or
   hash-injectivity premise was added to a replacement top.

Terminal/frame failed drafts are `.lean.txt`; the downstream MerkleTail draft
was never submitted and is uncredited. No failed draft enters the combined
import. The next deliverable is the SAME-resume Merkle parent, followed by the
source-ordered common converse, original tx2Op11 and exact corrected-host field.

target not yet established
