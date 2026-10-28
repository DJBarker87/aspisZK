import NCM_OuterRefinement
import NCM_BatchTypes

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_BatchCore
open Aeneas Aeneas.Std Result NCE_OpeningCuts NCM_BatchTypes
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def initial (s : Carrier) : Carrier := {s with scratch:=Port4B_BatchJoin.initial}

def child {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (ops : Ops) (batch : Nat) (folded : NCE_VerifierCuts.Digest) : NCM_OuterDirect.Child :=
  fun kind s => if bound : kind < 3 then
    NCM_Tree.execute D hash H ops.keys ops.leaf ops.count ops.padding ops.verifier batch
      (UScalar.ofNat kind (by scalar_tac)) (OraclePortSelectedDraft.capacity (3*batch+kind))
      (root s folded kind) (NCM_NodeViews.view s.proof batch kind) s
  else ([],false,s)

def execute {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (ops : Ops) (batch : Nat) (folded : NCE_VerifierCuts.Digest) (s : Carrier) :
    NCE_FirstFailure.Log × Option Nat × Carrier :=
  NCM_OuterDirect.execute ops.start ops.after0 ops.after1 ops.finish (child D hash H ops batch folded) (initial s)

def slot (parsed : OraclePortCompactDraft.Parsed) (s : Carrier) : NCE_FirstFailure.Slot :=
  fun batch kind scratch => MultiproofConeSlotState.slotState parsed (Port4B_KeyInstall.queries s.prepared.queries)
    batch kind (NCM_NodeViews.view s.proof batch kind) scratch

/-- One callee use with source-derived kind/slot/root domains. The child law
is proved from local fragments here; it is not a whole-tree native premise. -/
theorem child_agrees {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
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
    (batch : Nat) (bb : batch < 2) (s current : Carrier)
    (parsed : OraclePortCompactDraft.Parsed) (folded : NCE_VerifierCuts.Digest)
    (inputs : Inputs s parsed folded) (good : Good s current) (kind : Nat) (kb : kind < 3) :
    NCM_Tree.Agrees H (child D hash H ops batch folded kind current) (slot parsed s batch kind current.scratch) current ∧
      Good s (child D hash H ops batch folded kind current).2.2 := by
  let k : Usize := UScalar.ofNat kind (by scalar_tac)
  have kv : k.val = kind := rfl
  have size : current.proof.val.length = 57607 := by rw [good.2];exact inputs.proofLength
  have wire : parsed.wire = MultiproofConeCanonical.bytesOf current.proof.val := by rw [good.2];exact inputs.wire
  have queries : ∀ j, j < 22 → current.prepared.queries.val[j]!.val < 262144 := by rw [good.1];exact inputs.queries
  let index : Usize := UScalar.ofNat (3*batch+kind) (by scalar_tac)
  have nodes := NCM_NodeViews.source current.proof size parsed wire batch kind bb kb index rfl
  have associated := NCM_Tree.association D hash H oracle ops.keys keysZero keysWrite keysSort ops.leaf get opening leafCut
    ops.count countZero countCopy countScan countStore countHeight base ops.padding paddingCut ops.verifier row verifier admission
    batch k bb (by rw [kv];exact kb) current queries size parsed wire (root current folded kind)
    (by rw [kv];exact root_value s current parsed folded inputs good kind kb)
    (NCM_NodeViews.view current.proof batch kind) (by rw [kv];exact nodes.2)
    (by rw [kv];exact NCM_NodeViews.capacity batch kind bb kb)
  have agreement : NCM_Tree.Agrees H (child D hash H ops batch folded kind current)
      (slot parsed s batch kind current.scratch) current := by
    simpa only [child,dif_pos kb,slot,kv,good.1,good.2] using associated
  exact ⟨agreement,agreement.2.2.1.trans good.1,agreement.2.2.2.1.trans good.2⟩

#print axioms child_agrees
end AspisR1.NCM_BatchCore
end
