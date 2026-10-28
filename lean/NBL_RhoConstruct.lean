import NBL_PassConstruct
import NBA_Rho
set_option autoImplicit false
namespace AspisR1.NBL_RhoConstruct
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- No selected packed output is assumed: construct it and its SAME division
trace for every block, then derive the installed rho sampler call. -/
theorem source (block : Array U8 32#usize) :
    ∃ (digits : List Nat) (last : List UInt32) (q : aspis_core.field.QM31),
      LPk_Induction.Digits 4 (SamplerBytePass.digits block) digits last ∧
      NBA_Rho.coordinates q=digits ∧
      sampler.qm31_sample block=ok q := by
  obtain ⟨digits,last,division⟩ := NBL_PassConstruct.digits 4 (SamplerBytePass.digits block)
  obtain ⟨q,call,canonical,value⟩ := SamplerTransport.sample_total block
  have packed : NBA_Rho.coordinates q=digits :=
    value.trans (NBA_Rho.four_digits block digits last division).symm
  exact ⟨digits,last,q,division,packed,call⟩

#print axioms source
end AspisR1.NBL_RhoConstruct
