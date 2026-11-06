import NJL_EndpointCell
set_option autoImplicit false
namespace AspisR1.NJL_EndpointIndices
/-- Source offsets30/60 and the native lookup's bounds gc<30/pc<43. -/
def weight (gc : Fin 30) : Fin 103 := ⟨30+gc.val,by omega⟩
def pattern (pc : Fin 43) : Fin 103 := ⟨60+pc.val,by omega⟩
theorem disjoint (gc : Fin 30) (pc : Fin 43) : weight gc≠pattern pc := by
 intro equal
 have eq := congrArg Fin.val equal
 dsimp only [weight,pattern] at eq
 have := gc.isLt
 omega
theorem weight_domain (gc : Fin 30) : (weight gc).val≥30 ∧ (weight gc).val<60 := by
 dsimp only [weight]
 have := gc.isLt
 omega
theorem pattern_domain (pc : Fin 43) : (pattern pc).val≥60 ∧ (pattern pc).val<103 := by
 dsimp only [pattern]
 have := pc.isLt
 omega
#print axioms disjoint
#print axioms weight_domain
#print axioms pattern_domain
end AspisR1.NJL_EndpointIndices
