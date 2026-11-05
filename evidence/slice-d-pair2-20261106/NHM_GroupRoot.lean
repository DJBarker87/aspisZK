import NHM_GroupCoefficientDomain
import NHM_GroupAccumDomain
set_option autoImplicit false
namespace NHM_GroupRoot
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def initial : NHM_GroupCoefficient.Cells := Array.repeat 12#usize NHI_Scalar.zero

theorem initial_canonical : ∀ x∈initial.val,canonE x := by
 intro x hx
 simp only [initial,Array.repeat,List.mem_replicate] at hx
 rw [hx.2]
 exact NHI_Scalar.zero_canonical

def reference (f : Slice U8) (low : Array NE 16#usize) : Result NE := do
 let cells ← NHI_CountedLoop.unroll (NHM_GroupCoefficient.body f) 65
  ({start:=0#usize,«end»:=64#usize},initial)
 NHM_GroupAccum.reference low cells NHI_Scalar.zero

theorem cohort (f : Slice U8) (low : Array NE 16#usize) :
 FIo_Native.weights.s2_grouped_inactive_pair f low=reference f low := by
 unfold FIo_Native.weights.s2_grouped_inactive_pair reference
 simp only [NHM_GroupCoefficient.source,NHM_GroupAccum.source]
 rfl

theorem canonical (f : Slice U8) (low : Array NE 16#usize)
 (hl : ∀ x∈low.val,canonE x) (out : NE)
 (run : FIo_Native.weights.s2_grouped_inactive_pair f low=ok out) : canonE out := by
 rw [cohort] at run
 unfold reference at run
 obtain ⟨cells,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 have cc:=NHM_GroupCoefficientDomain.result f initial cells initial_canonical
  (by rwa [NHM_GroupCoefficient.source])
 exact NHM_GroupAccumDomain.result low hl cells cc NHI_Scalar.zero out NHI_Scalar.zero_canonical run

#print axioms initial_canonical
#print axioms cohort
#print axioms canonical
end NHM_GroupRoot
