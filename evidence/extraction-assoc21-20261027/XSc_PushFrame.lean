import XRr_PushFrame
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSc_PushFrame
/-- Any successful emitted push preserves raw-row length and the query term
counter, independent of canonicality or the checked-add proof route. -/
theorem source (b out : verifier.BatchedWeights) (i : Usize)
 (power : aspis_core.field.QM31) (basis : aspis_core.field.M31)
 (run : verifier.BatchedWeights.push b i power basis=ok out) :
 out.raw.val.length=b.raw.val.length ∧ out.terms=b.terms := by
 have terms := XRr_PushFrame.terms b out i power basis run
 unfold verifier.BatchedWeights.push at run
 obtain ⟨phase,_,run⟩ := bind_success _ _ _ run
 obtain ⟨old,back,hmut,run⟩ := pair_bind_success _ _ _ run
 rw [alloc.vec.Vec.index_mut_slice_index,alloc.vec.Vec.index_mut_usize] at hmut
 cases read : alloc.vec.Vec.index_usize b.raw i with
 | fail e => simp only [read] at hmut; cases hmut
 | div => simp only [read] at hmut; cases hmut
 | ok cell =>
  simp only [read] at hmut
  cases Result.ok.inj hmut
  obtain ⟨row,_,run⟩ := bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨by simp [alloc.vec.Vec.set],rfl⟩
#print axioms source
end XSc_PushFrame
