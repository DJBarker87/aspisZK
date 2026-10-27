import RPv_JGa_PatternInner
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_PatternOuter
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem source (n : Nat) (i limb : Usize) (a powers : Array field.QM31 16#usize)
    (result : Array field.QM31 14#usize) (span : i.val+n=14)
    (ha : canonical a) (hp : canonical powers) (hr : canonical result) :
    ∃ out,pattern_values_literal_loop1 a powers limb result i=ok out ∧ canonical out := by
  induction n generalizing i limb result with
  | zero =>
    refine ⟨result,?_,hr⟩
    rw [pattern_values_literal_loop1,POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1,if_neg (by scalar_tac : ¬(i<14#usize))]
  | succ n ih =>
    obtain ⟨p,hp1,hgood⟩ := WP.spec_imp_exists (JGa_ArrayProperty.read constants.COPY_PATTERNS i JGa_PatternBounds.Good (by change i.val<14;omega) JGa_PatternBounds.all)
    obtain ⟨value,hvalue,hvc⟩ := JGa_PatternInner.source 16 0#usize a powers p field.QM31.ZERO rfl ha hp FIv_NativeValue.zero.1 hgood
    obtain ⟨next,hn,hnc⟩ := JFy_ArrayTotal.update result i value (by change i.val<14;omega) hr hvc
    obtain ⟨i',hi,hiv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
    obtain ⟨out,tail,hout⟩ := ih i' 16#usize next (by change i'.val=i.val+1 at hiv;omega) hnc
    refine ⟨out,?_,hout⟩
    rw [pattern_values_literal_loop1,POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1,if_pos (by scalar_tac : i<14#usize),hp1,bind_tc_ok,hvalue,bind_tc_ok]
    change (do let next ← Array.update result i value; let i' ← i+1#usize; pattern_values_literal_loop1 a powers 16#usize next i')=ok out
    rw [hn,bind_tc_ok,hi,bind_tc_ok,tail]
#print axioms source
end AspisR1.JGa_PatternOuter
end
