import JFy_Steps
import JFy_ZeroArrays
import FIq_Native13
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_CopyPowers
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem source (n : Nat) (i : Usize) (lambda power : field.QM31)
    (a : Array field.QM31 16#usize) (span : i.val+n=16)
    (hl : Canon lambda) (hp : Canon power) (ha : canonical a) :
    ∃ out,pattern_values_literal_loop0 lambda a power i=ok (out,16#usize) ∧ canonical out := by
  induction n generalizing i power a with
  | zero =>
    have same : i=16#usize := UScalar.eq_of_val_eq (by change i.val=16;omega)
    subst i
    refine ⟨a,?_,ha⟩
    rw [pattern_values_literal_loop0,poseidon2.POSEIDON2_WIDTH,if_neg (by scalar_tac : ¬(16#usize<16#usize))]
  | succ n ih =>
    obtain ⟨next,hn,hnc⟩ := JFy_ArrayTotal.update a i power (by change i.val<16;omega) ha hp
    obtain ⟨power',hm,hmc,_⟩ := JFy_FieldTotal.mul power lambda hp hl
    obtain ⟨i',hi,hiv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
    obtain ⟨out,tail,hout⟩ := ih i' power' next (by change i'.val=i.val+1 at hiv;omega) hmc hnc
    refine ⟨out,?_,hout⟩
    rw [pattern_values_literal_loop0,poseidon2.POSEIDON2_WIDTH,if_pos (by scalar_tac : i<16#usize),hn,bind_tc_ok,hm,bind_tc_ok,hi,bind_tc_ok,tail]
#print axioms source
end AspisR1.JGa_CopyPowers
end
