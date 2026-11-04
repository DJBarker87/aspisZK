import NFG_TryInvCuts
set_option autoImplicit false
namespace NFG_InverseNone
open Aeneas Aeneas.Std Result NFG_InverseRef
/-- A returned None comes from the SAME zero test, never from a successful
nonzero child computation chosen independently. -/
theorem source (x : field.QM31) (none : field.QM31.try_inv x=ok Option.none) :
 field.QM31.is_zero x=ok true := by
 unfold field.QM31.try_inv at none
 obtain ⟨test,ht,run⟩ := NFG_ResultCongr.bind_success _ _ _ none
 cases test with
 | true => exact ht
 | false =>
  obtain ⟨aa,_,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨bb,_,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨rot,_,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨norm,_,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨inverse,_,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨real,_,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨negative,_,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨imag,_,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  cases run

theorem iff_zero (x : field.QM31) : field.QM31.try_inv x=ok none ↔ field.QM31.is_zero x=ok true :=
 ⟨source x,NFG_TryInvCuts.zero x⟩
#print axioms source
#print axioms iff_zero
end NFG_InverseNone
