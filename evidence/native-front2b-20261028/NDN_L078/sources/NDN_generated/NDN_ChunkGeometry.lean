import NDN_ArithmeticBounds
set_option autoImplicit false
namespace NDN_ChunkGeometry

theorem bounds (i e : Nat) (h:i<e) :
 i<min (i+4) e ∧ min (i+4) e≤e ∧ min (i+4) e≤i+4 :=
 ⟨lt_min (by omega) h,min_le_right _ _,min_le_left _ _⟩

theorem width (i e : Nat) (h:i<e) :
 1≤min (i+4) e-i ∧ min (i+4) e-i≤4 := by
 obtain ⟨a,b,c⟩:=bounds i e h
 omega

theorem decreases (i e : Nat) (h:i<e) :
 e-min (i+4) e<e-i := by
 obtain ⟨a,b,c⟩:=bounds i e h
 omega

theorem table_offsets (i e : Nat) (h:i<e) (he:e≤272) :
 i+4≤275 ∧ min (i+4) e≤272 ∧ i+1≤e := by
 have hh:=bounds i e h
 omega

#print axioms bounds
#print axioms width
#print axioms decreases
#print axioms table_offsets
end NDN_ChunkGeometry
