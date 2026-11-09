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
