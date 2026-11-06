import NJT_ClaimsRef_Value
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_ClaimsCohort
open Aeneas Aeneas.Std Result AspisR1ClaimsUnrolledParent
open NJT_ClaimsRef_Code NJT_ClaimsRef_Value

def triple (value : Row) : alloc.vec.Vec Row := ⟨[value,value,value],by simp;scalar_tac⟩

theorem parent_filled (value : Row) :
 aspis_core.r0.heap.filled external
  (Array.Insts.CoreMarkerCopy 29#usize aspis_core.field.QM31.Insts.CoreMarkerCopy)
  3#usize value = ok (.Ok (triple value)) := by
 let cq := aspis_core.field.QM31.Insts.CoreCloneClone
 have hq : ∀ q, cq.clone q = ok q := fun _ => rfl
 have row := clone_array 29#usize cq hq value
 obtain ⟨out,run,shape⟩ := WP.spec_imp_exists
  (alloc.vec.Vec.resize_spec (core.clone.CloneArray 29#usize cq)
   (alloc.vec.Vec.new Row) 3#usize value row)
 have same : out = triple value := by
  apply Subtype.ext
  simpa [alloc.vec.Vec.new,triple,List.resize] using shape
 change (do
  let out ← alloc.vec.Vec.resize (core.clone.CloneArray 29#usize cq)
    (alloc.vec.Vec.new Row) 3#usize value
  ok (core.result.Result.Ok out : core.result.Result (alloc.vec.Vec Row) aspis_core.r0.Error)) =
   ok (core.result.Result.Ok (triple value) : core.result.Result (alloc.vec.Vec Row) aspis_core.r0.Error)
 rw [run,same]
 rfl

theorem parent (pre : r1_wire.Prefix) :
 candidate_claims.claims external pre = decode pre := by
 rw [claims_value]
 unfold claimsReference decode
 cases h : ClaimsUnrolledFinish.sourceRecord pre 25#u8 with
 | fail e => simp [external,ClaimsUnrolledFinish.external,h]
 | div => simp [external,ClaimsUnrolledFinish.external,h]
 | ok result =>
  cases result with
  | Err e => simp [external,ClaimsUnrolledFinish.external,h,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
  | Ok record =>
    simp only [show external.validated pre 25#u8 = ok (.Ok record) from h]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,zero,bind_tc_ok]
    rw [parent_filled]
    simp [zero,mapError,external,ClaimsUnrolledFinish.external,std,boxArray,triple,
      core.result.Result.Insts.CoreOpsTry.branch]

/-- Complete safe-reference/cohort Result association. No external decoder,
Std dictionary, successful child reply or endpoint equation is a premise. -/
theorem reference (pre : r1_wire.Prefix) :
 unbox (NJT_ClaimsRef.r1_semantic.NJT_claims_ref pre) = candidate_claims.claims external pre := by
 rw [NJT_ClaimsRef_Value.reference,parent]

#print axioms parent_filled
#print axioms parent
#print axioms reference
end AspisR1.NJT_ClaimsCohort
end
