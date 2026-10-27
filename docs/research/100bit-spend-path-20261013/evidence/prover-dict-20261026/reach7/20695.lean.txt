import R1Z.PDict_CodecDictionary
set_option autoImplicit false
namespace R1Z.PDict_PureEqCM31
open Aeneas Aeneas.Std Result ProverRwFull

theorem exact (a b : aspis_core.field.CM31) :
    PDict_PureSource.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq a b = .ok true ↔ a = b := by
  cases a with
  | mk aa ab =>
    cases b with
    | mk ba bb =>
      by_cases h1 : aa = ba <;> by_cases h2 : ab = bb <;>
        simp [PDict_PureSource.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
          PDict_PureSource.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,h1,h2]

#print axioms exact
end R1Z.PDict_PureEqCM31
