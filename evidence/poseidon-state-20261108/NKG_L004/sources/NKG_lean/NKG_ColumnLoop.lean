import NKG_ColumnTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_ColumnLoop
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJe_ThreeColumnStep (Weights model)
open FJb_M31Step (Constants Bounded)
/-- Termination is on the sixteen-lane span; all weights and columns remain
fixed. One source iteration supplies the next state without a success premise. -/
theorem total (n : Nat) (i : Usize) (s : State) (w : Weights)
    (c0 c1 c2 : Constants) (span : i.val+n=16) (hw : canonical w)
    (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2) :
    ∃ out, state_only_poseidon.interpolate_three_constant_columns_loop w c0 c1 c2 s i=ok out := by
  induction n generalizing i s with
  | zero =>
    have stop : ¬i < poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
    exact ⟨s,by rw [FJe_ThreeColumnStep.unfold_loop,if_neg stop]⟩
  | succ n ih =>
    have hi : i.val < (16#usize).val := by change i.val<16;omega
    have guard : i < poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
    obtain ⟨next,rnext⟩ := NKG_ColumnTotal.step_total w c0 c1 c2 s i hi hw h0 h1 h2
    obtain ⟨i1,ri1,vi1⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
    change i1.val=i.val+1 at vi1
    obtain ⟨out,rout⟩ := ih i1 next (by omega)
    refine ⟨out,?_⟩
    rw [FJe_ThreeColumnStep.unfold_loop,if_pos guard,rnext,bind_tc_ok,ri1,bind_tc_ok]
    exact rout
/-- Complete emitted Result plus the existing adopted-model value theorem. -/
theorem source (w : Weights) (c0 c1 c2 : Constants) (hw : canonical w)
    (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2) :
    ∃ out, state_only_poseidon.interpolate_three_constant_columns w c0 c1 c2=ok out ∧
      canonical out ∧ decoded out=model w c0 c1 c2 := by
  obtain ⟨out,run⟩ := total 16 0#usize (Array.repeat 16#usize field.QM31.ZERO) w c0 c1 c2 rfl hw h0 h1 h2
  exact ⟨out,run,FJe_ThreeColumns.value w c0 c1 c2 out hw h0 h1 h2 run⟩
#print total
#print axioms total
#print source
#print axioms source
end AspisR1.NKG_ColumnLoop
end
