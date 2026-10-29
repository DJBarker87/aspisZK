import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CheckBaseLength60
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

theorem complete (column : Slice aspis_core.field.M31)
    (success : host_semantic.check_base_column column=ok (.Ok ())) :
    column.length=1024 := by
  by_cases h : Slice.len column=1024#usize
  · exact congrArg UScalar.val h
  · unfold host_semantic.check_base_column at success
    simp only [show (Slice.len column != 1024#usize)=true from by simp only [bne_iff_ne];exact h,
      if_true] at success
    cases success

#print axioms complete
end R1Z.PV_RunJoin_CheckBaseLength60
