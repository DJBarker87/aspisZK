import R1Z.PV_OWNI_RawConsumer
import R1Z.PV_RDB2D_SparseShape
set_option autoImplicit false
namespace R1Z.PV_OWNI_Scanner
open PV_OWNI_RawOps
/-- Literal raw equality, including all four limbs; never equality modulo P. -/
def equal (a b : Q) : Bool :=
 (a.c0.a.val==b.c0.a.val)&&(a.c0.b.val==b.c0.b.val)&&
 (a.c1.a.val==b.c1.a.val)&&(a.c1.b.val==b.c1.b.val)
def boolean (a : Q) : Bool := equal a zero || equal a one
def width (point : List Q) : Nat := PV_RDB2D_SparseShape.prefixLen boolean point
def trailing (point : List Q) : Nat := PV_RDB2D_SparseShape.trailing boolean point
/-- Big-endian suffix shift/OR. Zero and one are distinguished literally. -/
def bits : List Q → Nat
 | [] => 0
 | x::xs => (if equal x one then 1 else 0)*2^xs.length+bits xs
def suffix (point : List Q) : Nat := bits (point.drop (width point))

theorem bits_bound (xs : List Q) : bits xs<2^xs.length := by
 induction xs with
 | nil => change 0<1;omega
 | cons x xs ih =>
  rw [bits,List.length_cons,Nat.pow_succ]
  cases h:equal x one <;> simp only [h,Bool.false_eq_true,if_false,if_true] <;> omega

theorem split (point : List Q) (len:point.length=10) :
 width point+trailing point=10 := by
 rw [width,trailing,PV_RDB2D_SparseShape.split_length,len]

theorem suffix_bound (point : List Q) : suffix point<2^trailing point := by
 have h:=bits_bound (point.drop (width point))
 have split:=PV_RDB2D_SparseShape.split_length boolean point
 have hp:width point≤point.length := by unfold width PV_RDB2D_SparseShape.prefixLen;omega
 have len:(point.drop (width point)).length=trailing point := by
  rw [List.length_drop]
  change width point+trailing point=point.length at split
  omega
 simpa only [suffix,len] using h

#print axioms bits_bound
#print axioms split
#print axioms suffix_bound
end R1Z.PV_OWNI_Scanner
