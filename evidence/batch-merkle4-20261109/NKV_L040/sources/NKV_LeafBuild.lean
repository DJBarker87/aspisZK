import NKV_LeafInvocation
import NKL_LeafTotal
set_option autoImplicit false
noncomputable section
namespace NKV_LeafBuild
open Aeneas Aeneas.Std Result AspisR1
open MultiproofConeRef MultiproofConeLiveFold
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
abbrev HashState := AspisV8R19.SourceDuplexStep.State
abbrev History := List (Bytes × HashState)
abbrev Answer := Bool × reference.Scratch

def forget (out : Answer) : Option reference.Scratch := if out.1 then some out.2 else none

def leaves (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (kind : Nat) (positions : List Nat) : List Leaf :=
 positions.map (fun pos => (MultiproofConeLeafFold.key q kind pos,
   encodeState (H (OraclePortSelectedDraft.leaf p kind pos))))

/-- Direct source fold retaining the rejected scratch and exact queried prefix.
H on counterfactual suffixes is never added to History. -/
def build (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (kind : Nat) : List Nat → reference.Scratch → History × Result Answer
 | [],s => ([],ok (true,s))
 | pos::rest,s =>
   let request := OraclePortSelectedDraft.leaf p kind pos
   let digest := H request
   match reference.leaf_step s (MultiproofConeLeafFold.key q kind pos) (encodeState digest) with
   | .fail e => ([(request,digest)],fail e)
   | .div => ([(request,digest)],div)
   | .ok none => ([(request,digest)],ok (false,s))
   | .ok (some t) => let tail:=build H p q kind rest t;((request,digest)::tail.1,tail.2)

/-- Exact adopted leaf Program, including rejection and its absent suffix. -/
theorem adopted (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (kind : Nat) (positions : List Nat) (s : reference.Scratch) :
 eval H (MultiproofConeLeafFold.leaves p q kind positions s)=
 ((build H p q kind positions s).1,
   NKV_StepErasure.mapResult forget (build H p q kind positions s).2) := by
 induction positions generalizing s with
 | nil => rfl
 | cons pos rest ih =>
   simp only [MultiproofConeLeafFold.leaves,eval,build]
   cases step : reference.leaf_step s (MultiproofConeLeafFold.key q kind pos)
       (encodeState (H (OraclePortSelectedDraft.leaf p kind pos))) with
   | fail e => rfl
   | div => rfl
   | ok out =>
     cases out with
     | none => rfl
     | some t => rw [ih t]

theorem fold (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (kind : Nat) (positions : List Nat) (s : reference.Scratch) :
 NKV_StepErasure.mapResult forget (build H p q kind positions s).2=
 MultiproofConeLiveFold.fold (leaves H p q kind positions) s := by
 induction positions generalizing s with
 | nil => rfl
 | cons pos rest ih =>
   simp only [leaves,List.map_cons,MultiproofConeLiveFold.fold,build]
   cases step : reference.leaf_step s (MultiproofConeLeafFold.key q kind pos)
       (encodeState (H (OraclePortSelectedDraft.leaf p kind pos))) with
   | fail e => rfl
   | div => rfl
   | ok out =>
     cases out with
     | none => rfl
     | some t => exact ih t

/-- The SAME successful build supplies the NKB producer chain required by
its12-index/9216-byte caller theorem. No independent scratch is selected. -/
theorem chain (H : Bytes → HashState) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (kind : Nat) (positions : List Nat) (s after : reference.Scratch)
 (room : s.n.val+positions.length≤16)
 (accepted : (build H p q kind positions s).2=ok (true,after)) :
 NKB_LeafChain.Chain (leaves H p q kind positions) s (some after) := by
 obtain ⟨out,chain⟩:=NKL_LeafTotal.total (leaves H p q kind positions) s
   (by simpa only [leaves,List.length_map] using room)
 have exec : MultiproofConeLiveFold.fold (leaves H p q kind positions) s=ok (some after) := by
   rw [←fold H p q kind positions s,accepted]
   rfl
 have same : out=some after := Result.ok.inj
   ((NKB_LeafChain.source _ s out chain).symm.trans exec)
 rw [same] at chain
 exact chain

set_option pp.proofs false
#print adopted
#print chain
#print axioms adopted
#print axioms fold
#print axioms chain
end NKV_LeafBuild
end
