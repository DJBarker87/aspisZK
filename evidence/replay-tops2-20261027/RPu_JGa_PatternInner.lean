import RPu_JGa_PatternCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_PatternInner
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem unroll (a powers : Array field.QM31 16#usize) (i : Usize)
    (p : CompiledPoolV1PairForestPattern) (v : field.QM31) :
    pattern_values_literal_loop1_loop0 a powers i p v=(do
      if i<poseidon2.POSEIDON2_WIDTH then do
        let v' ← JGa_PatternCell.run a powers i p v
        let i' ← i+1#usize
        pattern_values_literal_loop1_loop0 a powers i' p v'
      else ok (i,v)) := by
  rw [pattern_values_literal_loop1_loop0]
  simp only [JGa_PatternCell.run,bind_assoc_eq]
#print axioms unroll

theorem source (n : Nat) (i : Usize) (a powers : Array field.QM31 16#usize)
    (p : CompiledPoolV1PairForestPattern) (v : field.QM31) (span : i.val+n=16)
    (ha : canonical a) (hp : canonical powers) (hv : Canon v) (hg : JGa_PatternBounds.Good p) :
    ∃ out,pattern_values_literal_loop1_loop0 a powers i p v=ok (16#usize,out) ∧ Canon out := by
  induction n generalizing i v with
  | zero =>
    have same : i=16#usize := UScalar.eq_of_val_eq (by change i.val=16;omega)
    subst i
    refine ⟨v,?_,hv⟩
    rw [unroll,poseidon2.POSEIDON2_WIDTH,if_neg (by scalar_tac : ¬(16#usize<16#usize))]
  | succ n ih =>
    obtain ⟨v',hc,hvc⟩ := WP.spec_imp_exists (JGa_PatternCell.source a powers i p v (by omega) ha hp hv hg)
    obtain ⟨i',hi,hiv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
    obtain ⟨out,tail,hout⟩ := ih i' v' (by change i'.val=i.val+1 at hiv;omega) hvc
    refine ⟨out,?_,hout⟩
    rw [unroll,poseidon2.POSEIDON2_WIDTH,if_pos (by scalar_tac : i<16#usize),hc,bind_tc_ok,hi,bind_tc_ok,tail]
#print axioms source
end AspisR1.JGa_PatternInner
end
