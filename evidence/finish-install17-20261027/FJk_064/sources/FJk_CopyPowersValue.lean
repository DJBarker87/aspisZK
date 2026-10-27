import JGa_CopyPowers
import FIw_ArrayValue
import FIw_WordValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_CopyPowersValue
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
/-- Symbolic power-array invariant for the original multiply/update loop. -/
theorem loop (n : Nat) (i : Usize) (lambda power : field.QM31)
    (a out : Array field.QM31 16#usize) (last : Usize)
    (span : i.val+n=16) (hl : Canon lambda) (hp : Canon power) (ha : canonical a)
    (powerValue : decode power=decode lambda^(i.val+1))
    (prior : ∀ j : Fin 16,j.val<i.val → decoded a j=decode lambda^(j.val+1))
    (run : pattern_values_literal_loop0 lambda a power i=ok (out,last)) :
    canonical out ∧ last=16#usize ∧ decoded out=fun j=>decode lambda^(j.val+1) := by
  induction n generalizing i power a with
  | zero =>
    have stop : ¬i<16#usize := by scalar_tac
    rw [pattern_values_literal_loop0,poseidon2.POSEIDON2_WIDTH,if_neg stop] at run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
    refine ⟨ha,UScalar.eq_of_val_eq (by change i.val=16;omega),?_⟩
    funext j
    exact prior j (by omega)
  | succ n ih =>
    have active : i<16#usize := by scalar_tac
    rw [pattern_values_literal_loop0,poseidon2.POSEIDON2_WIDTH,if_pos active] at run
    obtain ⟨a',ra,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨power',rp,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨i',ri,tail⟩ := FIv_Map.bind_success _ _ _ run
    have hi : i.val<(16#usize).val := by change i.val<16;omega
    have av := FIw_ArrayValue.update a a' i power hi ha hp ra
    have pv := FIv_NativeValue.mul power lambda power' hp hl rp
    have inc : i'.val=i.val+1 := FIw_WordValue.add i 1#usize i' ri
    apply ih i' power' a' (by omega) pv.1 av.1
    · rw [pv.2,powerValue,inc,←pow_succ]
    · intro j hj
      rw [av.2]
      by_cases he : j.val=i.val
      · have je : j=(⟨i.val,hi⟩ : Fin (16#usize).val) := Fin.ext he
        rw [je,Function.update_self,powerValue]
      · rw [Function.update_of_ne (fun h=>he (congrArg Fin.val h))]
        exact prior j (by omega)
    · exact tail
#print axioms loop
end AspisR1.FJk_CopyPowersValue
end
