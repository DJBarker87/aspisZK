import FJn_CopySmallMap
set_option autoImplicit false
namespace AspisR1.FJn_CopyPatternMap
variable {K L : Type} [Field K] [Field L]
attribute [local irreducible] R0P.copyPatterns
theorem value (f : K →+* L) (o : Fin 16 → K) (lambda : K) :
    (fun j=>f (R0P.copyPatternValuesLiteral o lambda j))=
      R0P.copyPatternValuesLiteral (fun i=>f (o i)) (f lambda) := by
  funext j
  unfold R0P.copyPatternValuesLiteral
  dsimp only
  rw [FJn_FoldMap.value f _ _
    (fun a i=>if (R0P.copyPatterns j).kinds i=1 then
      a+R0P.copyPowers (f lambda) i*(f (o ((R0P.copyPatterns j).columns i))+
        ((R0P.copyPatterns j).offsets i : L)) else a) (by
    intro a i
    split <;> simp only [map_add,map_mul,map_natCast,FJn_CopySmallMap.powers])]
  rw [map_zero]
#print axioms value
end AspisR1.FJn_CopyPatternMap
