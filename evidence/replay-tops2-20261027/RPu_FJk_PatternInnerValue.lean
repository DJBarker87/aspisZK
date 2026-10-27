import RPu_FJk_PatternCellValue
import RPu_JGa_PatternInner
import RPu_FIw_WordValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_PatternInnerValue
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
def indices : List (Fin 16) := List.ofFn id
def model (a powers : Array field.QM31 16#usize) (p : R0P.CopyPattern) (start : Nat) (seed : K) :=
  (indices.drop start).foldl (fun acc j=>FJk_PatternCellValue.step a powers p j acc) seed
/-- Whole actual16-cell pattern fold, by a symbolic suffix induction. -/
theorem value (n : Nat) (i last : Usize) (a powers : Array field.QM31 16#usize)
    (p : CompiledPoolV1PairForestPattern) (before out : field.QM31)
    (span : i.val+n=16) (ha : canonical a) (hp : canonical powers) (hb : Canon before)
    (hg : JGa_PatternBounds.Good p)
    (run : pattern_values_literal_loop1_loop0 a powers i p before=ok (last,out)) :
    Canon out ∧ last=16#usize ∧ decode out=model a powers (FJk_CopyPatternDescriptor.model p) i.val (decode before) := by
  induction n generalizing i before with
  | zero =>
    have stop : ¬i<16#usize := by scalar_tac
    rw [JGa_PatternInner.unroll,poseidon2.POSEIDON2_WIDTH,if_neg stop] at run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
    refine ⟨hb,UScalar.eq_of_val_eq (by change i.val=16;omega),?_⟩
    unfold model
    rw [List.drop_eq_nil_of_le (by simp only [indices,List.length_ofFn];omega)]
    rfl
  | succ n ih =>
    have active : i<16#usize := by scalar_tac
    rw [JGa_PatternInner.unroll,poseidon2.POSEIDON2_WIDTH,if_pos active] at run
    obtain ⟨next,rc,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨i',ri,tail⟩ := FIv_Map.bind_success _ _ _ run
    have hi : i.val<16 := by omega
    have one := FJk_PatternCellValue.value a powers p i before next hi ha hp hb hg rc
    have inc : i'.val=i.val+1 := FIw_WordValue.add i 1#usize i' ri
    have rest := ih i' next (by omega) one.1 tail
    refine ⟨rest.1,rest.2.1,?_⟩
    rw [rest.2.2,inc,one.2]
    unfold model
    have bound : i.val < indices.length := by simpa only [indices,List.length_ofFn] using hi
    rw [List.drop_eq_getElem_cons bound,List.foldl_cons]
    simp only [indices,List.getElem_ofFn,id_eq]
#print axioms value
end AspisR1.FJk_PatternInnerValue
end
