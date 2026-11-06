import NJX_DigestCohort
import NJX_AppendTargets
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_DigestView
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJX_DigestCohort (O D dc dcells)
def opened (o : O) (start : Usize) (hb : start.val+8≤16) (i : Fin 8) : NQ :=
 NJB_ArrayCarrier.cell o ⟨start.val+i.val,by have h:=i.isLt;scalar_tac⟩
def target (d : D) (right : Bool) (i : Fin 8) : Nat :=
 if right=true ∧ i.val=7 then ((dcells d i).val+1095962629)%2147483647 else (dcells d i).val
/-- SAME start/right of the actual emitted eight-lane binding. Arbitrary
canonical words, not bit-valued openings; no successful child hypothesis. -/
theorem source (high : NQ) (o : O) (d : D) (start : Usize) (right : Bool)
 (hb : start.val+8≤16) (hh : Canon high) (ho : FIw_ArrayValue.canonical o) (hd : dc d) :
 ∃ out,FIq_Native.pool_v1.pair_forest_semantic_terminal.add_digest_binding
  (Array.repeat 8#usize FIq_Native.field.QM31.ZERO) high o start d right=ok out ∧
 FIw_ArrayValue.canonical out ∧ ∀ i : Fin 8,
 FIw_ArrayValue.decoded out ⟨i.val,by have h:=i.isLt;scalar_tac⟩=
 decode high*(decode (opened o start hb i)-(target d right i : K)) := by
 have zero := JFy_ZeroArrays.source 8#usize
 obtain ⟨out,run,hout⟩ := WP.spec_imp_exists (JGa_DigestLoop.full _ high o start d right hb zero hh ho hd)
 have v := FIy_DigestBinding.value _ out high o start d right hb zero hh ho hd run
 refine ⟨out,run,hout,?_⟩
 intro i
 rw [v.2]
 simp only [FIw_ArrayValue.decoded,FIw_ArrayValue.cells,Array.repeat,List.getElem_replicate,FIv_NativeValue.zero.2,zero_add,
  FIy_DigestLane.increment,FIy_DigestLane.target,FIy_DigestTarget.value]
 unfold FIv_NativeArray.value opened target dcells NJB_ArrayCarrier.cell
 have bo : start.val+i.val<o.val.length := by rw [o.property];have h:=i.isLt;scalar_tac
 have bd : i.val<d.val.length := by rw [d.property];exact i.isLt
 rw [List.getElem?_eq_getElem bo,List.getElem?_eq_getElem bd]
 rfl
#print source
#print axioms source
end AspisR1.NKI_DigestView
end
