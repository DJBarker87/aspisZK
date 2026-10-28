import NBL_SamplerReplay
import NBA_ArrayEight
set_option autoImplicit false
namespace AspisR1.NBL_DecodeNative
open Aeneas Aeneas.Std Result
open AspisR1Post25Sampler
open ExtractedIndexedAddSmallNatModelV1

def digit (digits : Digits) (i : Fin 8) : U32 :=
  digits.val[i.val]'(by simpa [digits.property] using i.isLt)

def pack (d : Digits) : field.WideExact :=
  ⟨⟨⟨digit d 0,digit d 1⟩,⟨digit d 2,digit d 3⟩⟩,⟨⟨digit d 4,digit d 5⟩,⟨digit d 6,digit d 7⟩⟩⟩

theorem remainder (x : U32) (canonical : x.val<2147483647) :
    (x%field.P : Result U32)=ok x := by
  have same : (⟨BitVec.umod x.bv (2147483647#u32).bv⟩ : U32)=x := by
    apply UScalar.eq_of_val_eq
    change (x.bv%(2147483647#32)).toNat=x.bv.toNat
    rw [BitVec.toNat_umod]
    exact Nat.mod_eq_of_lt canonical
  unfold field.P
  change ok (⟨BitVec.umod x.bv (2147483647#u32).bv⟩ : U32)=ok x
  rw [same]

theorem canonical_qm (q : field.QM31)
    (a : q.c0.a.val<2147483647) (b : q.c0.b.val<2147483647)
    (c : q.c1.a.val<2147483647) (d : q.c1.b.val<2147483647) :
    field.canonical_qm31 q=ok q := by
  simp only [field.canonical_qm31,
    field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    remainder q.c0.a a,remainder q.c0.b b,remainder q.c1.a c,remainder q.c1.b d,bind_tc_ok]

/-- Exact coordinate law paired with the native canonical digit-packing gate.
No field equality is weakened to equality only after reduction. -/
theorem source (digits : Digits) (canonical : Canonical digits) :
    sampler.decode8 digits=ok (pack digits) := by
  have read (i : Usize) (hi : i.val<8) : Array.index_usize digits i=ok (digit digits ⟨i.val,hi⟩) :=
    NBA_ArrayEight.read digits i hi
  have bound (i : Fin 8) : (digit digits i).val<2147483647 := canonical i.val i.isLt
  have low := canonical_qm ⟨⟨digit digits 0,digit digits 1⟩,⟨digit digits 2,digit digits 3⟩⟩
    (bound 0) (bound 1) (bound 2) (bound 3)
  have high := canonical_qm ⟨⟨digit digits 4,digit digits 5⟩,⟨digit digits 6,digit digits 7⟩⟩
    (bound 4) (bound 5) (bound 6) (bound 7)
  simp only [sampler.decode8,read 0#usize (by decide),read 1#usize (by decide),read 2#usize (by decide),read 3#usize (by decide),read 4#usize (by decide),read 5#usize (by decide),read 6#usize (by decide),read 7#usize (by decide),
    field.CM31.new,field.WideExact.new,bind_tc_ok,pack]
  change (do
    let lo ← field.canonical_qm31 (pack digits).c0
    let hi ← field.canonical_qm31 (pack digits).c1
    ok (⟨lo,hi⟩ : field.WideExact))=ok (pack digits)
  dsimp only [pack]
  rw [low,bind_tc_ok,high,bind_tc_ok]

#print axioms remainder
#print axioms canonical_qm
#print axioms source
end AspisR1.NBL_DecodeNative
