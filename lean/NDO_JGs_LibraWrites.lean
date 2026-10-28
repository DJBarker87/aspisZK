import NDO_JGs_LibraEnd
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraWrites
open Aeneas Aeneas.Std Result
abbrev E := FIo_Install.NE
def after0 : Array E 4#usize := Array.make 4#usize [JGs_LibraEnd.a,
  FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,
  FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def after1 : Array E 4#usize := Array.make 4#usize [JGs_LibraEnd.a,JGs_LibraEnd.f,
  FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def after2 : Array E 4#usize := Array.make 4#usize [JGs_LibraEnd.a,JGs_LibraEnd.f,JGs_LibraEnd.h,
  FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
theorem one0 : FIo_Native.aspis_core.field.QM31.ONE=JGs_Libra.q0_0 := by with_unfolding_all rfl
#print axioms one0
theorem one1 : FIo_Native.aspis_core.field.QM31.ONE=JGs_Libra.q1_0 := by with_unfolding_all rfl
#print axioms one1
theorem up0 : Array.update JGs_LibraEnd.initial 0#usize JGs_LibraEnd.a=ok after0 := by with_unfolding_all rfl
#print axioms up0
theorem up1 : Array.update after0 1#usize JGs_LibraEnd.c=ok JGs_LibraEnd.middle := by with_unfolding_all rfl
#print axioms up1
theorem read : Array.index_usize JGs_LibraEnd.middle 1#usize=ok JGs_LibraEnd.c := by rfl
#print axioms read
theorem up2 : Array.update JGs_LibraEnd.middle 1#usize JGs_LibraEnd.f=ok after1 := by with_unfolding_all rfl
#print axioms up2
theorem up3 : Array.update after1 2#usize JGs_LibraEnd.h=ok after2 := by with_unfolding_all rfl
#print axioms up3
theorem up4 : Array.update after2 3#usize JGs_LibraEnd.j=ok JGs_LibraEnd.value := by with_unfolding_all rfl
#print axioms up4
end AspisR1.JGs_LibraWrites
end
