import NFG_NormNonzero
set_option autoImplicit false
namespace NFG_NormNatural
/-- Natural canonical-coordinate norm domain for the fixed CM31 backend. -/
theorem nonzero (a b : Nat) (ha : a<2147483647) (hb : b<2147483647)
 (live : ¬(a=0 ∧ b=0)) : (a*a+b*b)%2147483647≠0 := by
 have liveZ : ¬((a : ZMod 2147483647)=0 ∧ (b : ZMod 2147483647)=0) := by
  rintro ⟨za,zb⟩
  have aa := congrArg ZMod.val za
  have bb := congrArg ZMod.val zb
  have a0 : a=0 := by simpa [ZMod.val_natCast,Nat.mod_eq_of_lt ha] using aa
  have b0 : b=0 := by simpa [ZMod.val_natCast,Nat.mod_eq_of_lt hb] using bb
  exact live ⟨a0,b0⟩
 have field := NFG_NormNonzero.nonzero (a : ZMod 2147483647) (b : ZMod 2147483647) liveZ
 intro zero
 have castZero : ((a*a+b*b : Nat) : ZMod 2147483647)=0 := by
  apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr
  exact Nat.dvd_of_mod_eq_zero zero
 apply field
 simpa only [Nat.cast_add,Nat.cast_mul,pow_two] using castZero
#print axioms nonzero
end NFG_NormNatural
