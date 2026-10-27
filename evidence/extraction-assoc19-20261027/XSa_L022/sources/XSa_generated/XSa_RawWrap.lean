import XSa_QRawTotal
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSa_RawWrap

theorem wrap (n : Nat) (hn : n<18446744073709551616) : XRn_Join_wrap64 n=n :=
 Nat.mod_eq_of_lt hn

theorem sub (n m : Nat) (hn : n<18446744073709551616) (hm : m≤n) :
 XRn_Join_sub64 n m=n-m := by
 unfold XRn_Join_sub64 XRn_Join_wrap64
 have he : n+18446744073709551616-m=(n-m)+18446744073709551616 := by omega
 rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]

theorem partial (n : Nat) (hn : n<18446744073709551616) :
 XRn_Join_partial n=AspisR1BatchedFoldArithmetic.fold n := by
 unfold XRn_Join_partial XRn_Join_wrap64
 change (n%2147483648+n/2147483648)%18446744073709551616=n%2147483648+n/2147483648
 apply Nat.mod_eq_of_lt
 have hr := Nat.mod_lt n (by decide : 0<2147483648)
 have hd : n/2147483648<8589934592 := by omega
 omega

#print axioms wrap
#print axioms sub
#print axioms partial
end XSa_RawWrap
