import NJL_CachedPowers
import NJB_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_WindowStep
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIv_PreparedNew (NP)
def opened (o : Array NQ 16#usize) (start : Fin 9) (slot : Fin 8) : NQ :=
 NJB_ArrayCarrier.cell o ⟨start.val+slot.val,by have size : (16#usize).val=16 := by scalar_tac;rw [size];have := start.isLt;have := slot.isLt;omega⟩
/-- NJB_K102/K103: actual cache9words, actual opened[start+slot], one
Prepared product followed by one add, full scalar reply and next counter. -/
def Cut (cache : NP) (o : Array NQ 16#usize) (start : Fin 9) (slot : Fin 8)
 (before product reply after : NQ) (seenCache : NJB_PreparedCarrier.Index → NJB_PreparedCarrier.Index → U32)
 (seenOpened : NQ) (event : NJB_Cuts.Event) (calls next : Nat) : Prop :=
 calls=2 ∧ next=slot.val+1 ∧ seenCache=NJB_PreparedCarrier.words cache ∧
 seenOpened=opened o start slot ∧ event=⟨1,before,product⟩ ∧ after=reply
def reference (cache : NP) (o : Array NQ 16#usize) (start : Fin 9) (slot : Fin 8) (before : NQ) : Result NQ := do
 let product ← FIq_Native.field.PreparedQm31Multiplier.mul cache (opened o start slot)
 FIq_Native.field.QM31.add before product
/-- Generic same-cache domain SUPPORT; the eventual224 root must instantiate
this from NJL_CachedPowers, never expose Domain as a new row hypothesis. -/
theorem source (theta before : NQ) (cache : NP) (o : Array NQ 16#usize) (start : Fin 9) (slot : Fin 8)
 (ht : Canon theta) (hb : Canon before) (ho : FIw_ArrayValue.canonical o) (domain : NJB_PreparedLaws.Domain cache theta) :
 ∃ product reply,FIq_Native.field.PreparedQm31Multiplier.mul cache (opened o start slot)=ok product ∧
 FIq_Native.field.QM31.add before product=ok reply ∧ reference cache o start slot before=ok reply ∧
 Cut cache o start slot before product reply reply (NJB_PreparedCarrier.words cache) (opened o start slot)
  ⟨1,before,product⟩ 2 (slot.val+1) ∧ Canon reply ∧
 decode reply=decode before+decode theta*decode (opened o start slot) := by
 have oh : Canon (opened o start slot) := NJB_ArrayCarrier.canonical_cell o ho _
 obtain ⟨product,cp,hp,vp⟩ := NJB_PreparedLaws.mul_result cache theta (opened o start slot) ht oh domain
 obtain ⟨reply,cr,hr,vr⟩ := NJB_StubLaws.qm_add before product hb hp
 refine ⟨product,reply,cp,cr,?_,⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,hr,?_⟩
 · simp only [reference,cp,cr,bind_tc_ok]
 · rw [vr,vp]
#print source
#print axioms source
end AspisR1.NJL_WindowStep
end
