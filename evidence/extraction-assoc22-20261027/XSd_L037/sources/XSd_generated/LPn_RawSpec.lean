import Aeneas
set_option autoImplicit false
namespace AspisR1.LPn.RawSpec

def wrap64 (n : Nat) : Nat := n % 18446744073709551616
def sub64 (a b : Nat) : Nat := wrap64 (a+18446744073709551616-b)
def foldWord (n : Nat) : Nat := wrap64 (n%2147483648+n/2147483648)
def rawNat (a b c d e f g h : Nat) : List Nat :=
  let pp := 2147483647*2147483647
  let u := foldWord (sub64 (wrap64 (c*g+pp)) (d*h))
  let v := foldWord (wrap64 (c*h+d*g))
  [sub64 (wrap64 (sub64 (wrap64 (a*e+pp)) (b*f)+2*u+3*2147483647)) v,
   wrap64 (a*f+b*e+u+2*v),
   sub64 (sub64 (wrap64 (a*g+c*e+2*pp)) (b*h)) (d*f),
   wrap64 (a*h+b*g+c*f+d*e)]
end AspisR1.LPn.RawSpec
