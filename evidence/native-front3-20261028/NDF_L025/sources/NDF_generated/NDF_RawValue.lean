import NDF_RawRun
set_option autoImplicit false
namespace NDF_RawValue
open Aeneas Aeneas.Std Result

theorem total (N : Usize) (bytes : Slice U8) (offset : Usize)
    (fit : offset.val+N.val≤bytes.val.length) :
    ∃ out finish, NDF_ReaderRef.raw_ref N bytes offset=ok (out,finish) ∧
      out.val=(bytes.val.drop offset.val).take N.val ∧ finish.val=offset.val+N.val := by
  obtain ⟨out,run,all⟩ := NDF_RawRun.run bytes offset 0#usize (Array.repeat N 0#u8) fit
    (by scalar_tac) (NDF_RawState.initial _ _ _)
  obtain ⟨finish,add,value⟩ := WP.spec_imp_exists (Usize.add_spec (x:=offset) (y:=N) (by
    have := bytes.property
    omega))
  refine ⟨out,finish,?_,NDF_RawState.complete _ _ _ _ out.property fit all,value⟩
  simp only [NDF_ReaderRef.raw_ref,run,add,bind_tc_ok]

#print axioms total
end NDF_RawValue
