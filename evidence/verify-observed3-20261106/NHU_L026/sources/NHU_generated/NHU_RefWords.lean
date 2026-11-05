import NHU_MaskHelpers
set_option autoImplicit false
namespace AspisR1.NHU_RefWords
abbrev W := Nat×Nat
abbrev Good (x : W) := x.1<2147483647 ∧ x.2<2147483647
def iRef (x : W) : W := (NHU_MaskHelpers.negWord x.2,x.1)
def rRef (x : W) : W := NHU_MaskHelpers.rNative x.1 x.2

theorem i_relation (x : W) (canonical : x.2<2147483647) :
 iRef x=ExtractedMaskTowerBasis.iWords x := by
 change (NHU_MaskHelpers.negWord x.2,x.1)=((2147483647-x.2)%2147483647,x.1)
 exact congrArg (fun n=>(n,x.1)) (NHU_MaskHelpers.negWord_eq x.2 canonical)

theorem r_relation (x : W) (canonical : Good x) :
 rRef x=ExtractedMaskQM31Mul.rWords x :=
 NHU_MaskHelpers.rNative_eq x.1 x.2 canonical.1 canonical.2

theorem r_words_good (x : W) : Good (ExtractedMaskQM31Mul.rWords x) := by
 constructor
 · exact Nat.mod_lt _ (by omega)
 · exact Nat.mod_lt _ (by omega)

theorem r_good (x : W) (canonical : Good x) : Good (rRef x) := by
 rw [r_relation x canonical]
 exact r_words_good x

#print axioms i_relation
#print axioms r_relation
#print axioms r_words_good
#print axioms r_good
end AspisR1.NHU_RefWords
