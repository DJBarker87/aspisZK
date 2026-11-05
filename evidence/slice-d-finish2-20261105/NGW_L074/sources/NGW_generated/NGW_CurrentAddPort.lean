import RPt_FIo_M31Bridge
import RPz7_FIn_Polynomial
import NGW_PolynomialAdd
set_option autoImplicit false
namespace NGW_CurrentAddPort
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem cm (x y : NC) (hx : canonC x) (hy : canonC y) :
 (do let z ← FIo_Native.aspis_core.field.CM31.add x y;ok (FIo_FieldBridge.cm z))=
 AspisR1CurrentWide.field.CM31.add (FIo_FieldBridge.cm x) (FIo_FieldBridge.cm y) := by
 simp only [FIo_Native.aspis_core.field.CM31.add,AspisR1CurrentWide.field.CM31.add,FIo_FieldBridge.cm,bind_assoc_eq,bind_tc_ok]
 rw [FIo_M31Bridge.add x.a y.a hx.1 hy.1,FIo_M31Bridge.add x.b y.b hx.2 hy.2]
 rfl

theorem qm (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
 (do let z ← FIo_Native.aspis_core.field.QM31.add x y;ok (FIo_FieldBridge.qm z))=
 AspisR1CurrentWide.field.QM31.add (FIo_FieldBridge.qm x) (FIo_FieldBridge.qm y) := by
 simp only [FIo_Native.aspis_core.field.QM31.add,AspisR1CurrentWide.field.QM31.add,FIo_FieldBridge.qm]
 simp only [←cm x.c0 y.c0 hx.1 hy.1,←cm x.c1 y.c1 hx.2 hy.2,bind_assoc_eq,bind_tc_ok]

theorem wide (x y : NE) (hx : canonE x) (hy : canonE y) :
 (do let z ← FIo_Native.aspis_core.field.wide_exact.WideExact.add x y;ok (FIo_FieldBridge.wide z))=
 AspisR1CurrentWide.field.wide_exact.WideExact.add (FIo_FieldBridge.wide x) (FIo_FieldBridge.wide y) := by
 simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,AspisR1CurrentWide.field.wide_exact.WideExact.add,FIo_FieldBridge.wide]
 simp only [←qm x.c0 y.c0 hx.1 hy.1,←qm x.c1 y.c1 hx.2 hy.2,bind_assoc_eq,bind_tc_ok]

theorem adopted (x y : NE) (hx : canonE x) (hy : canonE y) :
 FIo_FieldBridge.map FIo_Install.fromE (FIo_Native.aspis_core.field.wide_exact.WideExact.add x y)=
 FIn_Primitives.add (FIo_Install.fromE x) (FIo_Install.fromE y) := by
 obtain ⟨z,run,_⟩ := NGW_PolynomialAdd.total x y hx hy
 have same := wide x y hx hy
 rw [run] at same
 simp only [bind_tc_ok] at same
 rw [run]
 change ok (FIo_Install.fromE z) = FIn_Primitives.add (FIo_Install.fromE x) (FIo_Install.fromE y)
 unfold FIn_Primitives.add
 change ok (FIo_Install.fromE z) =
   (do let out ← AspisR1CurrentWide.field.wide_exact.WideExact.add (FIo_FieldBridge.wide x) (FIo_FieldBridge.wide y)
       ok (SAQ_WideABI.fromW out))
 rw [←same]
 rfl

#print axioms cm
#print axioms qm
#print axioms wide
#print axioms adopted
end NGW_CurrentAddPort
