import R17GeometryClosedForms

/-! R17 table contents stay explicit P6 executable-certificate obligations.
No large table evaluation or native certificate is turned into a Lean axiom. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortJoinSplitR17
open AspisCircleGroupOrder AspisV7ExactOneFoldDomains FoldFactoredDomain FoldStoredGeometry

structure TableJoin (a b : Nat → C) : Prop where
  A : ∀ i, i < 512 → a i = tableA i
  B : ∀ i, i < 512 → b i = tableB i

theorem lookup_join (a b : Nat → C) (tables : TableJoin a b) (u : Fin 262144) :
    a (u.val &&& 511) * b (u.val >>> 9) = storedInitialFibrePoint20 u :=
  R17GeometryClosedForms.literal_lookup_to_stored a b tables.A tables.B u

theorem model_lookup (u : Fin 262144) :
    tableA (u.val &&& 511) * tableB (u.val >>> 9) = storedInitialFibrePoint20 u :=
  lookup_join tableA tableB ⟨fun _ _ => rfl, fun _ _ => rfl⟩ u

#print axioms lookup_join
#print axioms model_lookup
end AspisR1.OraclePortJoinSplitR17
end
