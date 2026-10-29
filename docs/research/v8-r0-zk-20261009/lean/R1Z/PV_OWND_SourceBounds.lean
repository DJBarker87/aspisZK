import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_SourceBounds
open PV_OWND_LegacySource

theorem private_aux (level : Nat) (h:level<21) :
 864≤aux level ∧ aux level+1<960 := by
 unfold aux
 omega

theorem private_rows (level : Nat) (h:level<21) :
 (3+level)*16+11<1024 ∧ (4+level)*16+12<1024 ∧ (4+level)*16<1024 := by omega

theorem append_rows (level : Nat) (h:level<20) :
 (33+level)*16+11<1024 ∧ (34+level)*16+12<1024 ∧ (34+level)*16<1024 := by omega

theorem helper_success (level : Nat) (h:level<21) : pathBase level=some (aux level) := by
 simp only [pathBase,h,ite_true]

theorem helper_failure (level : Nat) (h:21≤level) : pathBase level=none := by
 simp only [pathBase,show ¬level<21 by omega,ite_false]

/-- All source additions and multiplications above fit usize and u16. -/
theorem word_room (n : Nat) (h:n<1024) : n<65536 ∧ n<18446744073709551616 := by omega
#print axioms private_aux
#print axioms private_rows
#print axioms append_rows
#print axioms helper_success
#print axioms helper_failure
#print axioms word_room
end R1Z.PV_OWND_SourceBounds
