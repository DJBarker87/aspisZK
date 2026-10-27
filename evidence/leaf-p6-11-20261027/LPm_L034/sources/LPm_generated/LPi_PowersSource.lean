import LPi_PowersValue
set_option autoImplicit false
namespace AspisR1.LPi_PowersSource
open Aeneas Aeneas.Std Result LPi_FieldValues LPi_PowersPrefix

theorem one_canonical : canonE FIo_Native.aspis_core.field.wide_exact.WideExact.ONE := by
  norm_num [canonE,canonQ,canonC,LPi_CMProduct.Canon,
    FIo_Native.aspis_core.field.wide_exact.WideExact.ONE,
    FIo_Native.aspis_core.field.QM31.ONE,FIo_Native.aspis_core.field.QM31.ZERO]

theorem source (N : Usize) (x : NE) (hx : canonE x) :
    ∃ out, FIo_Native.weights.powers N x=ok out ∧ Holds out (ew x) N.val := by
  obtain ⟨out,run,meaning⟩ := LPi_PowersValue.loop x
    FIo_Native.aspis_core.field.wide_exact.WideExact.ONE
    (Array.repeat N FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO) 0#usize
    hx one_canonical (by scalar_tac) rfl (by intro j hj;exact (Nat.not_lt_zero j hj).elim)
  exact ⟨out,run,meaning⟩

theorem seven (x : NE) (hx : canonE x) :
    ∃ out, FIo_Native.weights.powers 7#usize x=ok out ∧ Holds out (ew x) 7 :=
  source 7#usize x hx

#print axioms one_canonical
#print axioms source
#print axioms seven
end AspisR1.LPi_PowersSource
