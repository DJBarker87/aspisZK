# NOC: exact A1 frontier after X3/X1

Target not yet established. Exact field, unchanged:
`RSL.TAS.NND_A1 (AspisR1.NNH_Run5bHost.S_host L0 copy std) NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C`.

Closed (support, not row credit): X3 `NOC_Op9.op9` (the former first open goal, verbatim);
X1 `NOC_MerkleBounded.parent/host/hostParent/model0`.

## X4 blocker: counterexample at S_host (needs a lead/owner decision)

X4 target (NNX_REMAINING X4, A12P item 2), stated on the SAME canonical inputs:
```lean
NNH_Tx1Returns.preparedValue ⟨pub, LIB_Carriers.bytes proof, g⟩ (envOf c) = .ok (p, g') →
verifier.candidate.prepare (DrvC_Installation.currentInstalled (configuration c))
  (NNV_PreparedAtHost.digest c) (AspisR1CurrentCaller.FirstComposition.toCurrentPublic pub)
  proof () none (NNV_PreparedInputs.scratch g) =
.ok (.Ok (InstalledPreparation.currentPrepared p), NNV_PreparedInputs.scratch g')
```
False whenever its premise holds: `NOC_PrepareDiv.prepare_div` proves the left side is `.div`
for every c and every input, because `(currentInstalled (configuration c)).op1 = fun _ _ _ => .div`
(`NOC_PrepareDiv.op1_div`, rfl). The slot comes unchanged from `NNH_HostSeed.m0.currentBase`
(`by constructor <;> intros <;> exact .div`) through `IDa_Deployed.seed`, and no installer
in the printed current chain overwrites op1 (L006). NNH_HostSeed's docstring says every
retained callable is overwritten or unused; op1 is retained and is used by 087.

Consequence for the field (argued, not yet a Lean theorem): on any input where the RSL
evaluator `NNH_Tx1Returns.value` returns `.ok`, the model's 094 `verifier.candidate.tx1`
passes the k/parse/scan/mark/ZERO steps and then calls this prepare, so model1 (stage1_owned)
diverges. The A1 Ok clause at S_host therefore holds only if no evaluator-accepting input exists.
A one-scope Lean statement of that (tx1/model1 = .div on the accepting prefix) is the natural
next deliverable if the lead wants the counterexample at field level.

Recommended repair (changes S_host's literal instantiation, so not taken here): install the
allocation slot op1 in the host's current base, matching the library child
`LIB_VLib.filledValue` (`if env.reservation then ok zeros else error`), as the JHe chain does
with `JGp_Allocation.base` (`{ops with op1 := filled}`). Then rebuild the host closure objects
that depend on S_host and re-run X4. By reading the installer sources (L006 prints plus
lean/Tx1Q_Install, Op3I/Op4P and the ConcreteConstants source; only op15 was also checked by
rfl, in L008), every other current slot used by tx1/prepare (op0, op2-op5, op7-op21) is
overwritten by an installer. I did not audit op6 or the stage/adapter dictionaries for the same defect.

## Not started (stopped after X4 per the brief)

X4 composition after a repair (ports exist: ConcreteConstants constants, NNG_Split087.split for
split_at_mut, NNH_Run5bCurrentExpand.semantic for op10, NGV_ExpandAssociation for op11,
NNV_PrepareView for op5, NOC_Op9.op9 for op9, NNX_PreparedValue.source for op8; still needed:
op1 port, Slice.index/Vec.index range lemmas against RSL `slice`/`LIBC_Bytes.raw`, and the
57607-byte proof domain from the 094 path).
X2 (SAQ_Decoder.read vs NFS_ReadCanonical.read, LIBC_QueryLoop link, NFS_PacketRoot.Domain),
X5/X6 (bind NNX_QueryOutput.domain/NNX_Flush.source/NNV_CurrentCheckpoint.source through 094;
NNX_CommonEncode.source through 345), X7 (094 Ok-iff), X8 (345 Ok-iff as in NNX_REMAINING),
X9 (AMN.viaReturns1 + toNND_A1, rfl example, raw ax2, NOC_FinalCombined) remain exactly as
stated in NNX_REMAINING.md. All are Lean-only. 22 of the 30 NOC scopes are unused.

target not yet established

# Update after the op1 repair (supersedes the X4 blocker above)

X4 is closed at the corrected configuration (`NOC_PrepareFront.source`, L015). The field is now
`RSL.TAS.NND_A1 (AspisR1.NOC_Run5bHost.S_host L0 copy std) NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C`;
no term exists. 35 of 50 scopes remain.

I paused before X2 without spending a scope, because reading the sources shows the remaining
phases need two kinds of lemma that no accepted root (NNV, NNX, NNY or NOC) provides:

1. X2 core: `SAQ_Decoder.read bytes i = NFS_ReadCanonical.read bytes i` for 128-byte openings and
   i < 4. The two sides are separate Aeneas extractions of the same Rust: the AspisR1RecordParser
   and FIo_Native `from_le_bytes`/`from_limbs` are token-identical modulo nominal types, but they
   differ in index arithmetic (checked `32*i`, `+32` versus wrapping `i*32`, `(i+1)*32`) and in their
   final carrier maps. A proof needs a bind-chain transport through 32 slice reads and 8 limb checks.
   It must then be carried through every op21 call reached inside `query_loop` under
   NFS_QueryInvariant, to get `query_loop (NFS_QueryOps.installed NJJ_QueryOps.concrete)` =
   `run (NFS_QueryLoopRoot.child (NFS_CallerDomains.select LIBC_QueryOps.seed) ..)`, the
   LIBC_QueryLoop link. The selections differ only in op21. Expect 3 or more scopes; the cap is 3.
2. Converse ports for X7/X8: the Ok-iff and the weak-Err clause need "model child returns Ok ⇒
   library child returns ok with the SAME value" for every 094/345 child (parse, scan, prepare
   front including semantic finish, batch, geometry, query loop, flush, checkpoint, codec, 345
   guards). Every accepted root, including NOC_Op9.op9 and NOC_PrepareFront.source, is the forward
   direction only. X7's cap of 3 and X8's cap of 2 cannot cover the converse of all children.

This is the shared obstruction of AGENTS §7 (the converse arm), so I stopped rather than spend
the extension on wrappers around it. Recommendation: fund a dedicated converse lane, one Ok-iff
or full Result equality per child, starting with the leaves whose library models already carry
exact Domain/model_exact equations (terminal, records, expansions, filled, view). Run X2's read
transport as its own capped item. Then resume X7-X9 here: 35 scopes remain, enough for X2,
X5/X6 and the assembly once the converse ports exist. If you want me to continue in strict order
anyway, X2 is next with its 3-scope cap.

target not yet established

# Update 2026-11-09 (after L040): exact frontier

Closed since the last update: 094 forward (`NOC_Tx1Forward.source`, L036) and the 345 Ok clause
(`NOC_Stage1Forward.ok345`, L040, labelled Ok clause only). NOM's two model lemmas are merged (66113b37590) and
used by reference; NOM's items 1 (public binding) and the op21 slot rfl are discharged inside L040. NOM's item 2
(LIBC_BatchMerkle.Domain on the 094 path) is not needed: both batch directions go through
NOC_MerkleBounded.hostParent / NOM_MerkleParent.hostParent, whose only hypotheses are k < 2 and the canonical
queries, which NOC_Tx1Forward derives from NNG_GeometryDomain094 on the SAME returned prepare law.

Open, in the lead's order:
1. Converse compositions (cap 14, none spent). Needed statement (weak-Err clause, AMN.viaReturns1.errT shape):
   `stage1_owned (S c) program xs data = .ok (.Ok saved) → NNH_ReturnsBundle.tx1Value ⟨key program,accounts xs,bytes data⟩ (envOf c) = .ok (bytes saved.deref)`
   (with ok345 this is the Ok-iff; contraposition gives errT). Chain, innermost first:
   (a) semantic finish converse: native op9 Ok ⇒ NNH_ObservedReturns.value ok, from NOC_ConvSemantic leaves plus
       NOM_TerminalDomain.terminal on the Domain from NOM_TerminalDomain.reached (its `same` premise is exactly
       publicBinding's equation, already proved in NOC_Stage1Forward);
   (b) prepare-front converse: native prepare Ok ⇒ library preparedValue ok with the SAME prep/scratch, from
       NOC_ConvLeaves (filled, expand_semantic, expand_values, view, prepared) and (a);
   (c) 094 converse: native tx1 Ok v ⇒ NNH_Tx1Returns.value ok (bytes v), from NOC_ConvLeaves.parse,
       NOC_Conv094 (scan, geometry, accNew, weightsNew), NOM_MerkleParent.hostParent (batch), NOC_QueryLink.loop
       on the Domain (NOC_QueryDomain.domain), flush/checkpoint total; the width premise again from the 345 guard;
   (d) 345 converse: inversion of NOC_Stage1Forward.body (every guard port there is an equality or has an exact
       library equation: route compare, distinct, readonly, checkpoint, getters, require_zero, decode/validate/encode
       via NNH_S1HostCodec/NMT_345 validate_iff, gate, first_decoded).
   Technique note: inversions must case-split each native call result; keep one declaration per call group
   (L038 showed the per-declaration heartbeat budget binds on whole-body proofs).
2. X9 (cap 8): restate NNV_WeakErrHost.modelRet1 at NOC_Run5bHost.S_host; okT from ok345 (map
   NNE_PhysicalAccepted.child1 / model1 c p e.first data to the tx1Ok carrier form), errT from 1 by
   contraposition; assemble AMN.viaReturns1 + toNND_A1; delivered-type rfl example; raw ax2 walk with the
   ledger29 walker; NOC_FinalCombined importing every NOC root (and NOM roots) in one scope.

target not yet established
