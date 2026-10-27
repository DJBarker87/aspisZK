import RPu_JGa_PatternOuter
import RPu_JGa_CopyPowers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_CopyPatterns
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

@[step] theorem source (a : Array field.QM31 16#usize) (lambda : field.QM31)
    (ha : canonical a) (hl : Canon lambda) : pattern_values a lambda ⦃ out => canonical out ⦄ := by
  obtain ⟨powers,hp,hpc⟩ := JGa_CopyPowers.source 16 0#usize lambda lambda _ rfl hl hl (JFy_ZeroArrays.source 16#usize)
  obtain ⟨out,ho,hoc⟩ := JGa_PatternOuter.source 14 0#usize 16#usize a powers _ rfl ha hpc (JFy_ZeroArrays.source 14#usize)
  have call : pattern_values a lambda=ok out := by
    unfold pattern_values pattern_values_literal
    dsimp only
    rw [hp,bind_tc_ok]
    exact ho
  rw [call]
  exact hoc
#print axioms source
end AspisR1.JGa_CopyPatterns
end
