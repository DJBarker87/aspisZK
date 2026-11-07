import NLT_NativeInvocation
import NKO_C07Source
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_QueryCapture
open Aeneas Aeneas.Std VTop_Stages

def Widths (b : NKE_QueryInput.Args) : Prop :=
 b.accumulator.weights.val.length=64 ∧ b.geometry.inverses.val.length=12 ∧
 b.geometry.line_z.val.length=12 ∧ b.pending.raw.val.length=64

def observation (b : NKE_QueryInput.Args) : NLB_Parent.QueryObservation where
 written := fun _ => 0#u8
 heap := fun n => b.proof.val[n]!
 logBase := b.proof.val.length
 logSize := 0
 proofBase := 0
 args := b

theorem view (b : Slice U8) :
 b.val=NKO_ReadonlyFrame.view (fun n=>b.val[n]!) 0 b.val.length := by
 unfold NKO_ReadonlyFrame.view
 apply List.ext_getElem
 · simp only [List.length_map,List.length_range]
 · intro i hi hj
   simp only [List.getElem_map,List.getElem_range,Nat.zero_add]
   exact (List.getElem!_pos b.val i hi).symm

/-- Payloads and disjoint write frame are constructed explicitly. No pointer
identity is used to infer a byte payload, and no native endpoint is assumed. -/
def input (b : NKE_QueryInput.Args) (widths : Widths b) : NLT_ParentCuts.Query b where
 observation := observation b
 frame := by
  refine ⟨view b.proof,Or.inl (Nat.le_refl _),?_,?_,?_,?_,widths.2.2.2,?_,rfl⟩
  · constructor <;> first | rfl | (intro i; rfl)
  · exact ⟨widths.1,fun _ _=>rfl,rfl,rfl,rfl⟩
  · intro i; rfl
  · exact ⟨rfl,widths.2.1,fun _ _=>rfl,widths.2.2.1,fun _ _=>rfl⟩
  · intro i hi; rfl
#print axioms view
#print axioms input
end AspisR1.NNH_QueryCapture
