import NCM_TailSlices
import NCM_CountCheck
import NCM_VerifierState

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_Tail
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts NCE_CarrierEffects
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

structure Verifier where
  node : Node
  entry : NCE_VerifierCuts.Entry
  exit : NCE_VerifierCuts.Exit
  finish : NCE_VerifierCuts.Finish
  pair : NCE_AdmissionCuts.Predicate
  range : NCE_AdmissionCuts.Predicate

def resetCursor (s : Carrier) : Carrier := {s with scratch:={s.scratch with «at»:=0#usize}}

def continued (verifier : Verifier) (root : NCE_VerifierCuts.Digest) (nodes : Slice U8)
    (count : Nat) (fallback : Carrier) : Result (Bool × Carrier) → Program Bytes State (Bool × Carrier)
  | .ok (accepted,s) => if accepted then
      NCM_Verifier.verify verifier.node verifier.entry verifier.exit verifier.finish verifier.pair verifier.range
        root (MultiproofConeSlotTail.prefixNodes nodes count) (resetCursor s)
    else .done (false,s)
  | _ => .done (false,fallback)

def run (count : NCM_CountCarrier.Ops) (padding : NCE_PaddingCuts.Body Carrier) (verifier : Verifier)
    (cap : Nat) (root : NCE_VerifierCuts.Digest) (nodes : Slice U8) (s : Carrier) : Program Bytes State (Bool × Carrier) :=
  match NCM_CountCarrier.count count verifier.pair verifier.range s with
  | none => .done (false,s)
  | some (used,after) => if used ≤ cap then
      continued verifier root nodes used after (NCM_PaddingRun.guard padding (NCM_TailSlices.suffix nodes used) after)
    else .done (false,after)

def model (cap : Nat) (root : NCE_VerifierCuts.Digest) (nodes : Slice U8) (s : Carrier) : Program Bytes State (Bool × Carrier) :=
  let indices := (MultiproofConePhysicalViews.live s.scratch 0 s.scratch.n.val).map Prod.fst
  if OraclePortFrozenOrder.wellFormed indices then
    let used := MultiproofConeSlotTail.slotCount s.scratch
    if used ≤ cap ∧ nodes.val.length = 32*cap ∧
      MultiproofConePadding.scan (4*(cap-used)) ((MultiproofConeCanonical.bytesOf nodes.val).drop (32*used)) = true then
      NCM_Verifier.model root (MultiproofConeSlotTail.prefixNodes nodes used) (resetCursor s)
    else .done (false,s)
  else .done (false,s)

/-- Count and padding results are derived before entering the verifier on
THAT same caller and the counted prefix. Every call domain is proved here. -/
theorem association {X Y : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (referenceD : aspis_core.digest.Digest32 Y) (hash : X) (referenceHash : Y)
    (H : Bytes → State)
    (oracle : ∀ input, referenceD.digest referenceHash input = ok (MultiproofConePhysicalTransport.rawOracle H input))
    (count : NCM_CountCarrier.Ops)
    (zero : NCE_CountInitCuts.NCE_Native_CountZero count.create)
    (copy : NCE_CountInitCuts.NCE_Native_CountCopy count.copy)
    (scan : NCE_CountCuts.NCE_Native_CountScan count.scan)
    (store : NCE_CountRowCuts.NCE_Native_CountCommit count.store)
    (height : NCE_CountLevelCuts.NCE_Native_CountHeight count.height)
    (base : Port3_NativeBatchBody.Ops) (padding : NCE_PaddingCuts.Body Carrier)
    (paddingCut : NCE_PaddingCuts.NCE_Native_Padding (NCM_PaddingPredicate.predicate base D) padding)
    (verifier : Verifier) (row : NCE_Native_Row H verifier.node)
    (control : NCE_VerifierCuts.NCE_Native_Verifier verifier.entry verifier.exit verifier.finish)
    (admission : NCE_AdmissionCuts.NCE_Native_Admission verifier.pair verifier.range)
    (cap : Nat) (bounded : cap ≤ 172) (root : NCE_VerifierCuts.Digest) (nodes : Slice U8)
    (size : nodes.val.length = 32*cap) (s : Carrier) :
    eval H (run count padding verifier cap root nodes s) = eval H (model cap root nodes s) := by
  have counted := NCM_CountCheck.association count zero copy scan store height verifier.pair verifier.range admission s
  unfold run
  rw [counted]
  unfold model
  dsimp only
  by_cases wf : OraclePortFrozenOrder.wellFormed ((MultiproofConePhysicalViews.live s.scratch 0 s.scratch.n.val).map Prod.fst)
  · simp only [wf,if_true]
    by_cases fit : MultiproofConeSlotTail.slotCount s.scratch ≤ cap
    · rw [if_pos fit]
      have padded := NCM_PaddingRun.observation base D padding paddingCut (NCM_TailSlices.suffix nodes (MultiproofConeSlotTail.slotCount s.scratch))
        (4*(cap-MultiproofConeSlotTail.slotCount s.scratch)) (NCM_TailSlices.suffix_length nodes _ cap fit size) s
      rw [padded,NCM_TailSlices.suffix_bytes]
      simp only [continued,size,fit,true_and]
      split
      · exact NCM_Verifier.association referenceD referenceHash H oracle verifier.node row verifier.entry verifier.exit verifier.finish control
          verifier.pair verifier.range admission root _ (resetCursor s)
          (by rw [NCM_TailSlices.prefix_length nodes _ cap fit size];omega) rfl
      · rfl
    · simp only [fit,false_and,if_false]
  · simp only [wf,if_false]

#print axioms association
end AspisR1.NCM_Tail
end
