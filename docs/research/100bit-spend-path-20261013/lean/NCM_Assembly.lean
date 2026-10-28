import NCM_BatchCore

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_Assembly
open Aeneas Aeneas.Std Result NCE_OpeningCuts NCM_BatchTypes
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Whole observation is a CONCLUSION only. Rejected scratch is not used as
an accepted next input, and the native rejected prefix remains in the log. -/
def Claim {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (ops : Ops) (batch : Nat) (folded : NCE_VerifierCuts.Digest)
    (s : Carrier) (parsed : OraclePortCompactDraft.Parsed) : Prop :=
  let source := NCM_BatchCore.execute D hash H ops batch folded s
  let target := NCE_FirstFailure.observe H (NCM_BatchCore.slot parsed s)
    [(batch,0),(batch,1),(batch,2)] Port4B_BatchJoin.initial
  source.1 = target.1 ∧ source.2.1 = target.2.1.map Prod.snd ∧
  source.2.2.prepared = s.prepared ∧ source.2.2.proof = s.proof ∧
  source.2.2.log = s.log++source.1 ∧
  (source.2.1 = none → source.2.2.scratch = target.2.2)

/-- Conditional same-execution batch theorem. The ONLY native hypotheses are
these 18 named NCE per-step families. The two redundant weak families remain
visible for the requested statement audit; neither is claimed discharged. -/
theorem bridge {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (oracle : ∀ input, D.digest hash input = ok (MultiproofConePhysicalTransport.rawOracle H input))
    (ops : Ops) (base : Port3_NativeBatchBody.Ops)

    (keysZero : NCE_KeyProducerCuts.NCE_Native_KeysZero ops.keys.create)
    (keysWrite : NCE_KeyCuts.NCE_Native_KeysWrite ops.keys.write)
    (keysSort : NCE_SortCarrierCuts.NCE_Native_KeysSortCarrier ops.keys.sort)
    (valueSort : NCE_SortCuts.NCE_Native_KeysSort ops.valueSort)
    (get : NCE_KeyReadCuts.NCE_Native_KeysRead ops.leaf.get)
    (opening : NCE_OpeningCuts.NCE_Native_Opening ops.leaf.reader)
    (leafCut : NCE_LeafCuts.NCE_Native_Leaf ops.leaf.request ops.leaf.post)
    (countZero : NCE_CountInitCuts.NCE_Native_CountZero ops.count.create)
    (countCopy : NCE_CountInitCuts.NCE_Native_CountCopy ops.count.copy)
    (countScan : NCE_CountCuts.NCE_Native_CountScan ops.count.scan)
    (countStore : NCE_CountRowCuts.NCE_Native_CountCommit ops.count.store)
    (countHeight : NCE_CountLevelCuts.NCE_Native_CountHeight ops.count.height)
    (paddingCut : NCE_PaddingCuts.NCE_Native_Padding (NCM_PaddingPredicate.predicate base D) ops.padding)
    (row : NCE_CarrierEffects.NCE_Native_Row H ops.verifier.node)
    (rowStore : NCE_RowStoreCuts.NCE_Native_RowStore ops.rowStore)
    (verifier : NCE_VerifierCuts.NCE_Native_Verifier ops.verifier.entry ops.verifier.exit ops.verifier.finish)
    (admission : NCE_AdmissionCuts.NCE_Native_Admission ops.verifier.pair ops.verifier.range)
    (outer : NCE_OuterCuts.NCE_Native_ThreeTrees ops.start ops.after0 ops.after1 ops.finish)
    (batch : Nat) (bb : batch < 2) (s : Carrier)
    (parsed : OraclePortCompactDraft.Parsed) (folded : NCE_VerifierCuts.Digest)
    (inputs : Inputs s parsed folded) : Claim D hash H ops batch folded s parsed := by
  have related := NCM_OuterRefinement.refinement H (NCM_BatchCore.child D hash H ops batch folded)
    (NCM_BatchCore.slot parsed s) batch (Good s) [0,1,2]
    (by
      intro kind member current good
      have kb : kind < 3 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        omega
      exact NCM_BatchCore.child_agrees D hash H oracle ops base keysZero keysWrite keysSort valueSort get opening leafCut countZero countCopy countScan countStore countHeight paddingCut row rowStore verifier admission outer
        batch bb s current parsed folded inputs good kind kb)
    (NCM_BatchCore.initial s) ⟨rfl,rfl⟩
  rw [←NCM_OuterRefinement.control ops.start ops.after0 ops.after1 ops.finish outer
    (NCM_BatchCore.child D hash H ops batch folded) (NCM_BatchCore.initial s)] at related
  rcases related with ⟨reads,first,good,log,final⟩
  exact ⟨reads,first,good.1,good.2,log,final⟩

#print Claim
#print bridge
#print axioms bridge
end AspisR1.NCM_Assembly
end
