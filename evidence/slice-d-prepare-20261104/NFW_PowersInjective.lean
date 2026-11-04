import NFW_PowersDomain
import RPu_FIp_PowersValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFW_PowersInjective
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues
abbrev decoded (x : NE) := AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide x)
theorem word (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647)
 (same : (a.val : ZMod 2147483647)=(b.val : ZMod 2147483647)) : a.val=b.val := by
 have h := congrArg ZMod.val same
 simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using h

theorem injective (x y : NE) (hx : canonE x) (hy : canonE y)
 (same : decoded x=decoded y) : x=y := by
 have h0 := congrArg (fun z : AspisWideTower.WideExact => z.re.re.re) same
 have h1 := congrArg (fun z : AspisWideTower.WideExact => z.re.re.im) same
 have h2 := congrArg (fun z : AspisWideTower.WideExact => z.re.im.re) same
 have h3 := congrArg (fun z : AspisWideTower.WideExact => z.re.im.im) same
 have h4 := congrArg (fun z : AspisWideTower.WideExact => z.im.re.re) same
 have h5 := congrArg (fun z : AspisWideTower.WideExact => z.im.re.im) same
 have h6 := congrArg (fun z : AspisWideTower.WideExact => z.im.im.re) same
 have h7 := congrArg (fun z : AspisWideTower.WideExact => z.im.im.im) same
 apply NFW_LPm_PowersBridge.values_injective
 exact Prod.ext (Prod.ext (Prod.ext (word _ _ hx.1.1.1 hy.1.1.1 h0) (word _ _ hx.1.1.2 hy.1.1.2 h1))
  (Prod.ext (word _ _ hx.1.2.1 hy.1.2.1 h2) (word _ _ hx.1.2.2 hy.1.2.2 h3)))
  (Prod.ext (Prod.ext (word _ _ hx.2.1.1 hy.2.1.1 h4) (word _ _ hx.2.1.2 hy.2.1.2 h5))
  (Prod.ext (word _ _ hx.2.2.1 hy.2.2.1 h6) (word _ _ hx.2.2.2 hy.2.2.2 h7)))
#print axioms word
#print axioms injective
end AspisR1.NFW_PowersInjective
