import NEB_AdditiveComposed
import NEB_WideSubRef
set_option autoImplicit false
namespace NEB_AdditiveFrames
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NEB_ArrayRefs

theorem m_add {S Event : Type} (state : S) (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.add x y=ok z ∧
      NEB_AdditiveRef.add_word (x) (y)=ok (z) ∧ z.val<2147483647 ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.M31.add x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add_word (x) (y))=ok (z,state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_AdditiveComposed.m_add x y hx hy
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩

theorem m_sub {S Event : Type} (state : S) (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.sub x y=ok z ∧
      NEB_AdditiveRef.sub_word (x) (y)=ok (z) ∧ z.val<2147483647 ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.M31.sub x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.sub_word (x) (y))=ok (z,state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_AdditiveComposed.m_sub x y hx hy
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩

theorem m_double {S Event : Type} (state : S) (x : U32) (hx : x.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.double x=ok z ∧
      NEB_AdditiveRef.add_word (x) (x)=ok (z) ∧ z.val<2147483647 ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.M31.double x)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add_word (x) (x))=ok (z,state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_AdditiveComposed.m_double x hx
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩

theorem cm_add {S Event : Type} (state : S) (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.add x y=ok z ∧
      NEB_AdditiveRef.add2 (wordsC x) (wordsC y)=ok (wordsC z) ∧ canonC z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.CM31.add x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add2 (wordsC x) (wordsC y))=ok (wordsC z,state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_AdditiveComposed.cm_add x y hx hy
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩

theorem cm_sub {S Event : Type} (state : S) (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.sub x y=ok z ∧
      NEB_AdditiveRef.sub2 (wordsC x) (wordsC y)=ok (wordsC z) ∧ canonC z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.CM31.sub x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.sub2 (wordsC x) (wordsC y))=ok (wordsC z,state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_AdditiveComposed.cm_sub x y hx hy
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩

theorem cm_double {S Event : Type} (state : S) (x : NC) (hx : canonC x) :
    ∃ z, FIo_Native.aspis_core.field.CM31.double x=ok z ∧
      NEB_AdditiveRef.add2 (wordsC x) (wordsC x)=ok (wordsC z) ∧ canonC z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.CM31.double x)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add2 (wordsC x) (wordsC x))=ok (wordsC z,state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_AdditiveComposed.cm_double x hx
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩

theorem qm_add {S Event : Type} (state : S) (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.add x y=ok z ∧
      NEB_AdditiveRef.add4 (wordsQ x) (wordsQ y)=ok (wordsQ z) ∧ canonQ z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.QM31.add x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add4 (wordsQ x) (wordsQ y))=ok (wordsQ z,state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_AdditiveComposed.qm_add x y hx hy
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩

theorem qm_sub {S Event : Type} (state : S) (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.sub x y=ok z ∧
      NEB_AdditiveRef.sub4 (wordsQ x) (wordsQ y)=ok (wordsQ z) ∧ canonQ z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.QM31.sub x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.sub4 (wordsQ x) (wordsQ y))=ok (wordsQ z,state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_AdditiveComposed.qm_sub x y hx hy
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩

theorem wide_add {S Event : Type} (state : S) (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z ∧
      NEB_AdditiveRef.add8 (wordsE x) (wordsE y)=ok (wordsE z) ∧ canonE z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.WideExact.add x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add8 (wordsE x) (wordsE y))=ok (wordsE z,state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_AdditiveComposed.wide_add x y hx hy
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩

theorem wide_sub {S Event : Type} (state : S) (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z : NE,
      AspisR1CurrentWide.field.wide_exact.WideExact.sub
        (NBG_GetterPorts.wide x) (NBG_GetterPorts.wide y)=ok (NBG_GetterPorts.wide z) ∧
      NEB_AdditiveRef.sub8 (wordsE x) (wordsE y)=ok (wordsE z) ∧ canonE z ∧
      NEB_PureFrame.run (Event:=Event) state (AspisR1CurrentWide.field.wide_exact.WideExact.sub
        (NBG_GetterPorts.wide x) (NBG_GetterPorts.wide y))=ok (NBG_GetterPorts.wide z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.sub8 (wordsE x) (wordsE y))=
        ok (wordsE z,state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_WideSubRef.result x y hx hy
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩
#print axioms m_add
#print axioms m_sub
#print axioms m_double
#print axioms cm_add
#print axioms cm_sub
#print axioms cm_double
#print axioms qm_add
#print axioms qm_sub
#print axioms wide_add
#print axioms wide_sub
end NEB_AdditiveFrames
