import R1Z.PV_OWNI_Scanner
set_option autoImplicit false
namespace R1Z.PV_OWNI_SuffixLoop
open PV_OWNI_Scanner PV_OWNI_RawOps
/-- The deployed increasing-coordinate suffix loop, with its actual incoming
accumulator, equals the big-endian symbolic suffix encoding. -/
theorem fold (xs : List Q) (acc : Nat) :
 xs.foldl (fun a x=>2*a+(if equal x one then 1 else 0)) acc=
 acc*2^xs.length+bits xs := by
 induction xs generalizing acc with
 | nil => simp only [List.foldl_nil,List.length_nil,Nat.pow_zero,Nat.mul_one,bits,Nat.add_zero]
 | cons x xs ih =>
  rw [List.foldl_cons,ih,bits,List.length_cons,Nat.pow_succ,Nat.add_mul]
  have mul:(2*acc)*2^xs.length=acc*(2^xs.length*2) := by ac_rfl
  rw [mul]
  omega

theorem suffix (point : List Q) :
 (point.drop (width point)).foldl
 (fun a x=>2*a+(if equal x one then 1 else 0)) 0=PV_OWNI_Scanner.suffix point := by
 rw [fold]
 simp only [Nat.zero_mul,Nat.zero_add,PV_OWNI_Scanner.suffix]
#print axioms fold
#print axioms suffix
end R1Z.PV_OWNI_SuffixLoop
