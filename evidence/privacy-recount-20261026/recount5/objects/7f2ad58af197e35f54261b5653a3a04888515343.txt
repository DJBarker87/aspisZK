import R1Z.PV_CBL_FinalizeSoftValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FinalizeSoftTotal
set_option autoImplicit false
theorem total (state : Array U32 8#usize) (blocks : U64)
    (buffer : Array U8 64#usize) (pos : Usize) (hp : pos.val<64) :
    ∃ output, PV_CBL_FinalSoft.sha_finalize_soft_owned state blocks buffer pos=ok output := by
  obtain ⟨first,second,hr,_⟩ := PV_CBL_FinalizeSoftValue.source state blocks buffer pos hp
  exact ⟨_,hr⟩
theorem no_fail (state : Array U32 8#usize) (blocks : U64)
    (buffer : Array U8 64#usize) (pos : Usize) (hp : pos.val<64) (error : Error) :
    PV_CBL_FinalSoft.sha_finalize_soft_owned state blocks buffer pos≠fail error := by
  obtain ⟨out,hr⟩ := total state blocks buffer pos hp
  rw [hr]
  intro h
  cases h
#print axioms total
#print axioms no_fail
end R1Z.PV_CBL_FinalizeSoftTotal
