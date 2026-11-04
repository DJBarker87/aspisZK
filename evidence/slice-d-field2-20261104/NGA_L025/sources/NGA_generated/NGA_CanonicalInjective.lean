import NGA_NativeOps
set_option autoImplicit false
noncomputable section
namespace NGA_CanonicalInjective
open Aeneas Aeneas.Std Result AspisR1.FIo_FieldBridge
abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev Q := AspisV8R15.ExactTowerBase.QM31Exact

theorem word (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647)
 (h : (a.val : M)=(b.val : M)) : a=b := by
 apply UScalar.eq_of_val_eq
 have hv := congrArg (fun z : M => z.val) h
 simpa only [ZMod.val_natCast_of_lt ha,ZMod.val_natCast_of_lt hb] using hv

theorem qm (x y : NQ) (hx : NGA_NativeOps.Canon x) (hy : NGA_NativeOps.Canon y)
 (h : NGA_NativeOps.decode x=NGA_NativeOps.decode y) : x=y := by
 have h00 := congrArg (fun z : Q => z.re.re) h
 have h01 := congrArg (fun z : Q => z.re.im) h
 have h10 := congrArg (fun z : Q => z.im.re) h
 have h11 := congrArg (fun z : Q => z.im.im) h
 change (x.c0.a.val : M)=(y.c0.a.val : M) at h00
 change (x.c0.b.val : M)=(y.c0.b.val : M) at h01
 change (x.c1.a.val : M)=(y.c1.a.val : M) at h10
 change (x.c1.b.val : M)=(y.c1.b.val : M) at h11
 exact congrArg₂ FIo_Native.aspis_core.field.QM31.mk
   (congrArg₂ FIo_Native.aspis_core.field.CM31.mk (word _ _ hx.1.1 hy.1.1 h00) (word _ _ hx.1.2 hy.1.2 h01))
   (congrArg₂ FIo_Native.aspis_core.field.CM31.mk (word _ _ hx.2.1 hy.2.1 h10) (word _ _ hx.2.2 hy.2.2 h11))

theorem wide (x y : NE) (hx : AspisR1.FIo_WideValues.Canon x) (hy : AspisR1.FIo_WideValues.Canon y)
 (h : AspisR1CurrentWide.Proof.decodeWide (AspisR1.FIo_FieldBridge.wide x)=
      AspisR1CurrentWide.Proof.decodeWide (AspisR1.FIo_FieldBridge.wide y)) : x=y := by
 have h0 := congrArg (fun z : AspisWideTower.WideExact => z.re) h
 have h1 := congrArg (fun z : AspisWideTower.WideExact => z.im) h
 exact congrArg₂ FIo_Native.aspis_core.field.wide_exact.WideExact.mk
   (qm x.c0 y.c0 hx.1 hy.1 h0) (qm x.c1 y.c1 hx.2 hy.2 h1)

#print axioms word
#print axioms qm
#print axioms wide
end NGA_CanonicalInjective
end
