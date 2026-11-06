import NJB_PreparedLaws
import RPv_FIw_ScalarArithmetic
import NJL_Traverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_DigestResiduals
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
abbrev Digest := Fin 8 → U32
abbrev Residuals := Fin 8 → NQ
/-- Full lift/sub pair in the frozen globally ordered residual prefix. -/
def Cell (o : Residuals) (d : Digest) (i : Fin 8) (x : NQ) : Prop :=
 FIq_Native.pool_v1.pair_forest_semantic_terminal.lift_m31 (d i)=ok (FIw_ScalarArithmetic.lifted (d i)) ∧
 FIq_Native.field.QM31.sub (o i) (FIw_ScalarArithmetic.lifted (d i))=ok x

def reference (o : Residuals) (d : Digest) (i : Fin 8) : Result NQ := do
 let target ← FIq_Native.pool_v1.pair_forest_semantic_terminal.lift_m31 (d i)
 FIq_Native.field.QM31.sub (o i) target

theorem cell (o : Residuals) (d : Digest) (ho : ∀ i,Canon (o i)) (hd : ∀ i,(d i).val<2147483647) (i : Fin 8) :
 ∃ x,reference o d i=ok x ∧ Cell o d i x ∧ Canon x ∧ decode x=decode (o i)-((d i).val : K) := by
 have lift := FIw_ScalarArithmetic.lift_run (d i)
 have lv := FIw_ScalarArithmetic.lift_value (d i) (hd i)
 obtain ⟨x,cx,hx,vx⟩ := NJB_StubLaws.qm_sub (o i) (FIw_ScalarArithmetic.lifted (d i)) (ho i) lv.1
 exact ⟨x,by simp only [reference,lift,bind_tc_ok,cx],⟨lift,cx⟩,hx,by rw [vx,lv.2]⟩

/-- All8 SAME actual residual Results, in source order, before either pack or
product. The child clauses are derived; no opaque reply becomes a premise. -/
theorem source (o : Residuals) (d : Digest) (ho : ∀ i,Canon (o i)) (hd : ∀ i,(d i).val<2147483647) :
 ∃ (xs : {xs : List NQ // xs.length=(List.finRange 8).length}),
 NJB_Traverse.run (reference o d) (List.finRange 8)=ok xs ∧
 (∀ x∈xs.val,Canon x) ∧ List.Forall₂ (Cell o d) (List.finRange 8) xs.val := by
 apply NJL_Traverse.packet
 intro i _
 obtain ⟨x,cx,cl,hx,_⟩ := cell o d ho hd i
 exact ⟨x,cx,hx,cl⟩
#print source
#print axioms cell
#print axioms source
end AspisR1.NJX_DigestResiduals
end
