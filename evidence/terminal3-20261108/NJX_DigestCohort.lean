import NJX_DigestGroups
import NDO_JGa_DigestLoop
import RPv_FIy_DigestBinding
import RPv_JFy_ZeroArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_DigestCohort
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
abbrev O := Array NQ 16#usize
abbrev D := Array U32 8#usize
def ocells (o : O) (i : Fin 8) : NQ := NJB_ArrayCarrier.cell o ⟨i.val,by have h:=i.isLt;scalar_tac⟩
def dcells (d : D) (i : Fin 8) : U32 := NJB_ArrayCarrier.cell d ⟨i.val,by have h:=i.isLt;scalar_tac⟩
def dc (d : D) : Prop := ∀ x∈d.val,x.val<2147483647
/-- Complete old emitted eight-lane binding at ZERO, retaining the SAME
high/opened/expected. This model law is not a native bridge for an old helper. -/
theorem source (high : NQ) (o : O) (d : D) (hh : Canon high)
 (ho : FIw_ArrayValue.canonical o) (hd : dc d) :
 ∃ out,FIq_Native.pool_v1.pair_forest_semantic_terminal.add_digest_binding
  (Array.repeat 8#usize FIq_Native.field.QM31.ZERO) high o 0#usize d false=ok out ∧
 FIw_ArrayValue.canonical out ∧ ∀ i : Fin 8,
 FIw_ArrayValue.decoded out ⟨i.val,by have h:=i.isLt;scalar_tac⟩=
 decode high*(decode (ocells o i)-((dcells d i).val : K)) := by
 have zero := JFy_ZeroArrays.source 8#usize
 obtain ⟨out,run,hout⟩ := WP.spec_imp_exists (JGa_DigestLoop.full _ high o 0#usize d false (by decide) zero hh ho hd)
 have v := FIy_DigestBinding.value _ out high o 0#usize d false (by decide) zero hh ho hd run
 refine ⟨out,run,hout,?_⟩
 intro i
 rw [v.2]
 simp only [FIw_ArrayValue.decoded,FIw_ArrayValue.cells,Array.repeat,List.getElem_replicate,FIv_NativeValue.zero.2,zero_add,
  FIy_DigestLane.increment,FIy_DigestLane.target,FIy_DigestTarget.value,Bool.false_eq_true,if_false,
  show (0#usize).val=0 from rfl,Nat.zero_add]
 unfold FIv_NativeArray.value ocells dcells NJB_ArrayCarrier.cell
 have bo : i.val<o.val.length := by
  rw [o.property]
  have h:=i.isLt
  scalar_tac
 have bd : i.val<d.val.length := by
  rw [d.property]
  exact i.isLt
 rw [List.getElem?_eq_getElem bo,List.getElem?_eq_getElem bd]
 rfl
#print source
#print axioms source
end AspisR1.NJX_DigestCohort
end
