import NEB_ArrayRefs
import NEB_AdditiveCalls
import NEB_PureFrame
set_option autoImplicit false
namespace NEB_AdditiveComposed
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NEB_ArrayRefs

theorem m_add (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.add x y=ok z ∧
      NEB_AdditiveRef.add_word x y=ok z ∧ z.val<2147483647 := by
  obtain ⟨z,run,_,cz⟩ := LPi_NatBase.add x y hx hy
  exact ⟨z,run,(NEB_WordRefs.add x y).trans run,cz⟩

theorem m_sub (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.sub x y=ok z ∧
      NEB_AdditiveRef.sub_word x y=ok z ∧ z.val<2147483647 := by
  obtain ⟨z,run,_,cz⟩ := LPi_NatBase.sub x y hx hy
  exact ⟨z,run,(NEB_WordRefs.sub x y).trans run,cz⟩

theorem m_double (x : U32) (hx : x.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.double x=ok z ∧
      NEB_AdditiveRef.add_word x x=ok z ∧ z.val<2147483647 := by
  obtain ⟨z,run,ref,cz⟩ := m_add x x hx hx
  exact ⟨z,by simpa only [FIo_Native.aspis_core.field.M31.double] using run,ref,cz⟩

theorem cm_add (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.add x y=ok z ∧
      NEB_AdditiveRef.add2 (wordsC x) (wordsC y)=ok (wordsC z) ∧ canonC z := by
  obtain ⟨z,run,cz,_⟩ := LPi_FieldValues.cm_add x y hx hy
  exact ⟨z,run,by rw [NEB_ArrayRefs.cm_add,run];rfl,cz⟩

theorem cm_sub (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.sub x y=ok z ∧
      NEB_AdditiveRef.sub2 (wordsC x) (wordsC y)=ok (wordsC z) ∧ canonC z := by
  obtain ⟨z,run,cz,_⟩ := LPi_FieldValues.cm_sub x y hx hy
  exact ⟨z,run,by rw [NEB_ArrayRefs.cm_sub,run];rfl,cz⟩

theorem cm_double (x : NC) (hx : canonC x) :
    ∃ z, FIo_Native.aspis_core.field.CM31.double x=ok z ∧
      NEB_AdditiveRef.add2 (wordsC x) (wordsC x)=ok (wordsC z) ∧ canonC z := by
  obtain ⟨z,run,ref,cz⟩ := cm_add x x hx hx
  exact ⟨z,by simpa only [FIo_Native.aspis_core.field.CM31.double] using run,ref,cz⟩

theorem qm_add (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.add x y=ok z ∧
      NEB_AdditiveRef.add4 (wordsQ x) (wordsQ y)=ok (wordsQ z) ∧ canonQ z := by
  obtain ⟨z,run,cz,_⟩ := LPi_TowerValues.qm_add x y hx hy
  exact ⟨z,run,by rw [NEB_ArrayRefs.qm_add,run];rfl,cz⟩

theorem qm_sub (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.sub x y=ok z ∧
      NEB_AdditiveRef.sub4 (wordsQ x) (wordsQ y)=ok (wordsQ z) ∧ canonQ z := by
  obtain ⟨z,run,cz,_⟩ := LPi_TowerValues.qm_sub x y hx hy
  exact ⟨z,run,by rw [NEB_ArrayRefs.qm_sub,run];rfl,cz⟩

theorem wide_add (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z ∧
      NEB_AdditiveRef.add8 (wordsE x) (wordsE y)=ok (wordsE z) ∧ canonE z := by
  obtain ⟨z,run,cz,_⟩ := NBG_WideCarriers.wide_add x y hx hy
  exact ⟨z,run,by rw [NEB_ArrayRefs.wide_add,run];rfl,cz⟩

#print axioms m_add
#print axioms m_sub
#print axioms m_double
#print axioms cm_add
#print axioms cm_sub
#print axioms cm_double
#print axioms qm_add
#print axioms qm_sub
#print axioms wide_add
end NEB_AdditiveComposed
