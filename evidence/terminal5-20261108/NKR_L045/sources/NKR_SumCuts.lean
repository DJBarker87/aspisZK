import NKR_SumCohort
set_option autoImplicit false
noncomputable section
namespace NKR_SumCuts
open Aeneas Aeneas.Std Result
open NKR_SumDispatch

/-- Reviewed transcription of NKR_sum_dispatch_cut in NKR_Sum_native.rs.txt:
one entered child, arity=count, selected SAME left/right cells, complete
four-word output equal to its opaque child reply. The harness proves every
word with arbitrary limb<4. No field arithmetic claim is part of this cut.
Its file hash and exact assertion lines are pinned by NKR_Sum_TRANSCRIPTION.json. -/
def Cut (l r : A4) (count : Nat) (seek : Fin 4) (reply out seenLeft seenRight : Q)
 (calls arity : Nat) : Prop :=
 1≤count ∧ count≤4 ∧ seek.val<count ∧ calls=1 ∧ arity=count ∧
 seenLeft=NGA_Indexed.selected l seek ∧ seenRight=NGA_Indexed.selected r seek ∧ out=reply

/-- Complete SAME-call invocation: all child-result clauses are discharged
with CLOSED field helper laws before the cut reply is instantiated. No
native log, child success, endpoint equality or Ops record is a hypothesis. -/
theorem source (l r : A4) (count : Nat) (lower : 1≤count) (upper : count≤4)
 (hl : ∀ q∈l.val,Canon q) (hr : ∀ q∈r.val,Canon q) :
 ∃ out,native l r count=ok out ∧ reference l r count=ok out ∧
 NKJ_Cohort.run ((l.val.zip r.val).take count)=ok out ∧ Canon out ∧
 AspisR1.ExtractedMaskQM31Exact.decode out=NGA_SumAlgebra.sumProducts ((l.val.zip r.val).take count) ∧
 ∀ (seek : Fin 4),seek.val<count →
 Cut l r count seek out out (NGA_Indexed.selected l seek) (NGA_Indexed.selected r seek) 1 count := by
 obtain ⟨out,hn,hrun,hcohort,hc,hv⟩ := NKR_SumCohort.result l r count lower upper hl hr
 exact ⟨out,hn,hrun,hcohort,hc,hv,fun seek hs=>⟨lower,upper,hs,rfl,rfl,rfl,rfl,rfl⟩⟩

#print source
#print axioms source
end NKR_SumCuts
end
