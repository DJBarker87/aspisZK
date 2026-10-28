import NCM_Assembly

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_Batch
open Aeneas Aeneas.Std Result NCE_OpeningCuts NCM_BatchTypes
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- TX1 batch 0: exact accept/first-error and chronological-prefix
observation from the SAME Prepared/proof/caller; 18 explicit native step
families only, plus runtime oracle interpretation and original input facts. -/
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
    (s : Carrier) (parsed : OraclePortCompactDraft.Parsed) (folded : NCE_VerifierCuts.Digest)
    (inputs : Inputs s parsed folded) : NCM_Assembly.Claim D hash H ops 0 folded s parsed :=
  NCM_Assembly.bridge D hash H oracle ops base keysZero keysWrite keysSort valueSort get opening leafCut countZero countCopy countScan countStore countHeight paddingCut row rowStore verifier admission outer 0 (by decide) s parsed folded inputs

#print bridge
#print axioms bridge
end AspisR1.NCM_Batch
end
