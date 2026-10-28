import RPt_FIo_WideValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_WideAdd
open Aeneas Aeneas.Std Result

theorem base (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.add a b=ok z ∧ z.val<2147483647 := by
  obtain ⟨z,run,_,canon⟩ := ExtractedCurrentM31AddSub.current_add_mod a b ha hb
  refine ⟨z,?_,canon⟩
  rw [FIo_M31Bridge.add a b ha hb,AspisR1CurrentWide.Proof.m31_add_same]
  exact run

theorem cm (a b : FIo_Native.aspis_core.field.CM31) (ha : FIo_CMValues.Canon a) (hb : FIo_CMValues.Canon b) :
    ∃ z, FIo_Native.aspis_core.field.CM31.add a b=ok z ∧ FIo_CMValues.Canon z := by
  obtain ⟨x,hx,cx⟩ := base a.a b.a ha.1 hb.1
  obtain ⟨y,hy,cy⟩ := base a.b b.b ha.2 hb.2
  exact ⟨⟨x,y⟩,by simp only [FIo_Native.aspis_core.field.CM31.add,hx,hy,bind_tc_ok],⟨cx,cy⟩⟩

theorem qm (a b : FIo_Native.aspis_core.field.QM31) (ha : FIo_QMValues.Canon a) (hb : FIo_QMValues.Canon b) :
    ∃ z, FIo_Native.aspis_core.field.QM31.add a b=ok z ∧ FIo_QMValues.Canon z := by
  obtain ⟨x,hx,cx⟩ := cm a.c0 b.c0 ha.1 hb.1
  obtain ⟨y,hy,cy⟩ := cm a.c1 b.c1 ha.2 hb.2
  exact ⟨⟨x,y⟩,by simp only [FIo_Native.aspis_core.field.QM31.add,hx,hy,bind_tc_ok],⟨cx,cy⟩⟩

theorem source (a b : FIo_Install.NE) (ha : FIo_WideValues.Canon a) (hb : FIo_WideValues.Canon b) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.add a b=ok z ∧ FIo_WideValues.Canon z := by
  obtain ⟨x,hx,cx⟩ := qm a.c0 b.c0 ha.1 hb.1
  obtain ⟨y,hy,cy⟩ := qm a.c1 b.c1 ha.2 hb.2
  exact ⟨⟨x,y⟩,by simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,hx,hy,bind_tc_ok],⟨cx,cy⟩⟩

#print axioms base
#print axioms cm
#print axioms qm
#print axioms source
end AspisR1.JFs_TX2_WideAdd
end
