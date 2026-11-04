import NFF_RawTypedLog
import NFG_ArrayWindow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_RawCoupling
open Aeneas Aeneas.Std Result
abbrev Q := NFF_RawTypedLog.Q
abbrev Words := Array U64 4#usize

def values (raw : Words) : Nat × Nat × Nat × Nat :=
 (raw.val[0]!.val,raw.val[1]!.val,raw.val[2]!.val,raw.val[3]!.val)

/-- The native raw-result equation is the arbitrary-coordinate assertion of
NFF_K019, on the same local replies. It is not a whole-callee model equality. -/
theorem native_result (a b : Q) (ha : NFE_NFC_RawValues.Canon a)
 (hb : NFE_NFC_RawValues.Canon b) (products : NFF_RawLog.Log)
 (law : ∀ i,NEG_ProductAbstraction.Product 64
  (NFF_RawLog.operands (NFF_RawTypedLog.words a) (NFF_RawTypedLog.words b) i).1
  (NFF_RawLog.operands (NFF_RawTypedLog.words a) (NFF_RawTypedLog.words b) i).2 (products i))
 (raw : Words) (native : values raw=NFF_RawLog.evaluate products) :
 FIo_Native.fast_pairing.canonical.Q.raw a b=ok raw := by
 obtain ⟨r0,r1,r2,r3,shape⟩ := NFC_ArrayFour.shape raw
 subst raw
 obtain ⟨m0,m1,m2,m3,source,value⟩ := NFF_RawTypedLog.replay a b ha hb products law
 have observed := value.trans native.symm
 simp only [values,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ,Prod.mk.injEq] at observed
 rcases observed with ⟨v0,v1,v2,v3⟩
 have e0 : m0=r0 := UScalar.eq_of_val_eq v0
 have e1 : m1=r1 := UScalar.eq_of_val_eq v1
 have e2 : m2=r2 := UScalar.eq_of_val_eq v2
 have e3 : m3=r3 := UScalar.eq_of_val_eq v3
 simpa only [e0,e1,e2,e3] using source
#print axioms native_result
end AspisR1.NFG_RawCoupling
end
