import LPh_NativeTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPh.Native
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC NQ NE cm qm wide)

def cWords (x : AspisV8R15.ExactTowerBase.CM31Exact) : Nat × Nat := (x.re.val,x.im.val)
def qWords (x : AspisV8R15.ExactTowerBase.QM31Exact) := (cWords x.re,cWords x.im)
def eWords (x : AspisWideTower.WideExact) := (qWords x.re,qWords x.im)
def nativeCWords (x : NC) : Nat × Nat := (x.a.val,x.b.val)
def nativeQWords (x : NQ) := (nativeCWords x.c0,nativeCWords x.c1)
def nativeEWords (x : NE) := (nativeQWords x.c0,nativeQWords x.c1)

theorem cWords_decode (x : NC) (hx : FIo_CMValues.Canon x) :
    cWords (decodeC (cm x)) = nativeCWords x := by
  change ((x.a.val : ZMod 2147483647).val,(x.b.val : ZMod 2147483647).val) = _
  rw [ZMod.val_natCast_of_lt hx.1,ZMod.val_natCast_of_lt hx.2]
  rfl

theorem qWords_decode (x : NQ) (hx : FIo_QMValues.Canon x) :
    qWords (decodeQM (qm x)) = nativeQWords x := by
  change (cWords (decodeC (cm x.c0)),cWords (decodeC (cm x.c1))) = _
  rw [cWords_decode x.c0 hx.1,cWords_decode x.c1 hx.2]
  rfl

theorem eWords_decode (x : NE) (hx : FIo_WideValues.Canon x) :
    eWords (decodeWide (wide x)) = nativeEWords x := by
  change (qWords (decodeQM (qm x.c0)),qWords (decodeQM (qm x.c1))) = _
  rw [qWords_decode x.c0 hx.1,qWords_decode x.c1 hx.2]
  rfl

theorem cm_mul_words (x y : NC) (hx : FIo_CMValues.Canon x) (hy : FIo_CMValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y=ok z ∧ FIo_CMValues.Canon z ∧
      nativeCWords z=cWords (decodeC (cm x)*decodeC (cm y)) := by
  obtain ⟨z,hz⟩ := cm_mul_total x y
  have v := FIo_CMMulValues.mul x y z hx hy hz
  exact ⟨z,hz,v.1,(cWords_decode z v.1).symm.trans (congrArg cWords v.2)⟩

theorem qm_mul_words (x y : NQ) (hx : FIo_QMValues.Canon x) (hy : FIo_QMValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul x y=ok z ∧ FIo_QMValues.Canon z ∧
      nativeQWords z=qWords (decodeQM (qm x)*decodeQM (qm y)) := by
  obtain ⟨z,hz⟩ := qm_mul_total x y
  have v := FIo_QMMulValues.mul x y z hx hy hz
  exact ⟨z,hz,v.1,(qWords_decode z v.1).symm.trans (congrArg qWords v.2)⟩

theorem by_r_words (x : NC) (hx : FIo_CMValues.Canon x) :
    ∃ z, FIo_Native.aspis_core.field.mul_by_r x=ok z ∧ FIo_CMValues.Canon z ∧
      nativeCWords z=cWords (AspisV8R15.ExactTowerBase.qm31R*decodeC (cm x)) := by
  obtain ⟨z,hz⟩ := by_r_total x
  have v := FIo_ByRValues.value x z hx hz
  exact ⟨z,hz,v.1,(cWords_decode z v.1).symm.trans (congrArg cWords v.2)⟩

theorem wide_mul_words (x y : NE) (hx : FIo_WideValues.Canon x) (hy : FIo_WideValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z ∧ FIo_WideValues.Canon z ∧
      nativeEWords z=eWords (decodeWide (wide x)*decodeWide (wide y)) := by
  obtain ⟨z,hz,hc,hv⟩ := wide_mul_value x y hx hy
  exact ⟨z,hz,hc,(eWords_decode z hc).symm.trans (congrArg eWords hv)⟩

#print axioms cWords_decode
#print axioms qWords_decode
#print axioms eWords_decode
#print axioms cm_mul_words
#print axioms qm_mul_words
#print axioms by_r_words
#print axioms wide_mul_words
end AspisR1.LPh.Native
end
