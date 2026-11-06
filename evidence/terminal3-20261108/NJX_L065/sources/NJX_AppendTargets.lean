import NJX_DigestResiduals
import NJB_TagReduce
import NJB_ArrayCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_AppendTargets
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_DigestResiduals (Digest Residuals)
def tweak : U32 := 1095962629#u32
/-- Actual right-group1 final M31.add, full natural modular value and
canonical domain, discharges NJL_K057/058's target-tweak stub. -/
theorem source (d : Digest) (hd : ∀ i,(d i).val<2147483647) :
 ∃ target,FIq_Native.field.M31.add (d 7) tweak=ok target ∧
 target.val=((d 7).val+1095962629)%2147483647 ∧
 ∀ i : Fin 8,(if i=7 then target else d i).val<2147483647 := by
 obtain ⟨target,ct,vt,ht⟩ := NJB_TagReduce.add (d 7) tweak (hd 7) (by decide)
 refine ⟨target,ct,vt,?_⟩
 intro i
 split <;> first|exact ht|exact hd i

def right (o : Array NQ 16#usize) (i : Fin 8) : NQ := NJB_ArrayCarrier.cell o ⟨8+i.val,by have h:=i.isLt;scalar_tac⟩
/-- All actual opened[8+4group+j] words, with no extra caller restriction. -/
theorem canonical (o : Array NQ 16#usize) (ho : FIw_ArrayValue.canonical o) : ∀ i,Canon (right o i) :=
 fun i=>NJB_ArrayCarrier.canonical_cell o ho _
#print source
#print axioms source
#print axioms canonical
end AspisR1.NJX_AppendTargets
end
