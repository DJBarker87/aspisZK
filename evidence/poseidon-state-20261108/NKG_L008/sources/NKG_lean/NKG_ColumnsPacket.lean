import NKG_ColumnCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_ColumnsPacket
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJe_ThreeColumnStep (Weights model)
open FJb_M31Step (Constants Bounded)
/-- Same finite native-cut trace after CLOSED children are substituted at the
logged arguments. Source execution is a conclusion, never a root premise. -/
theorem loop (w : Weights) (c0 c1 c2 : Constants) (states : Nat → State)
 (cut : NKG_ColumnCuts.Trace w c0 c1 c2 states)
 (hw : canonical w) (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2)
 (n : Nat) (i : Usize) (span : i.val+n=16) :
 state_only_poseidon.interpolate_three_constant_columns_loop w c0 c1 c2 (states i.val) i=ok (states 16) := by
 induction n generalizing i with
 | zero =>
   have stop : ¬ i<poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
   rw [FJe_ThreeColumnStep.unfold_loop,if_neg stop]
   have eq : i.val=16 := by omega
   rw [eq]
 | succ n ih =>
   have hi : i.val<16 := by omega
   have guard : i<poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
   obtain ⟨next,calls,args,stage⟩ := cut.steps ⟨i.val,hi⟩
   have idx : Usize.ofNat i.val (by scalar_tac)=i := UScalar.eq_of_val_eq rfl
   have frame : states (i.val+1)=(states i.val).set i (NKG_ColumnReply.reply w c0 c1 c2 ⟨i.val,hi⟩) := by
     simpa only [idx] using stage.frame
   obtain ⟨i1,ri1,vi1⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
   change i1.val=i.val+1 at vi1
   have rest := ih i1 (by omega)
   rw [FJe_ThreeColumnStep.unfold_loop,if_pos guard,
     NKG_ColumnReply.step_reply w c0 c1 c2 (states i.val) i hi hw h0 h1 h2,bind_tc_ok,
     ←frame,ri1,bind_tc_ok]
   simpa only [vi1] using rest
/-- Complete raw output, canonicality and adopted value for TX1:321. Native
cut transcriptions and input domains are the only non-headline hypotheses. -/
theorem source (w : Weights) (c0 c1 c2 : Constants) (states : Nat → State)
 (hw : canonical w) (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2)
 (cut : NKG_ColumnCuts.Trace w c0 c1 c2 states) :
 state_only_poseidon.interpolate_three_constant_columns w c0 c1 c2=ok (states 16) ∧
 canonical (states 16) ∧ decoded (states 16)=model w c0 c1 c2 := by
 have run := loop w c0 c1 c2 states cut hw h0 h1 h2 16 0#usize rfl
 change state_only_poseidon.interpolate_three_constant_columns_loop w c0 c1 c2 (states 0) 0#usize=ok (states 16) at run
 rw [cut.initial] at run
 exact ⟨run,FJe_ThreeColumns.value w c0 c1 c2 (states 16) hw h0 h1 h2 run⟩
#print loop
#print axioms loop
#print source
#print axioms source
end AspisR1.NKG_ColumnsPacket
end
