import AspisV8R19.FullWitnessPointCode

/-! Literal ordered scatter of the 271 G coefficients. The full low
functional depends only on coin 0; other semantic coefficients are arbitrary. -/
namespace AspisR19.SparseGScatter
open AspisV8R17 T163SourceTable SourceMaskTransport FullPointFunctional FullQuotientWeights
noncomputable section
variable {F : Type*} [CommRing F]

theorem updates_at {I J : Type*} [DecidableEq I] [DecidableEq J]
    (rows : List I) (index : I → J) (hi : Function.Injective index)
    (coins : I → F) (out : J → F) (i : I) :
    (rows.foldl (fun w j => Function.update w (index j) (coins j)) out) (index i)=
      if i∈rows then coins i else out (index i) := by
  induction rows generalizing out with
  | nil => simp
  | cons j rows ih =>
    rw [List.foldl_cons,ih]
    by_cases hm : i∈rows
    · simp [hm]
    · by_cases he : i=j
      · subst i; simp [hm]
      · simp [hm,he,show index i≠index j from fun h => he (hi h)]

theorem updates_off {I J : Type*} [DecidableEq J]
    (rows : List I) (index : I → J) (coins : I → F) (out : J → F) (r : J)
    (hr : ∀ i∈rows, r≠index i) :
    (rows.foldl (fun w j => Function.update w (index j) (coins j)) out) r=out r := by
  induction rows generalizing out with
  | nil => rfl
  | cons j rows ih =>
    rw [List.foldl_cons,ih _ (fun i h => hr i (by simp [h]))]
    exact Function.update_of_ne (hr j (by simp)) _ _

def original (coins : Fin 271 → F) : Fin 1024 → F :=
  (List.finRange 271).foldl (fun w i => Function.update w (order (coinIndex i)) (coins i)) (fun _ => 0)

theorem coinIndex_injective : Function.Injective coinIndex := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [coinIndex] at this
  omega

theorem original_at (coins : Fin 271 → F) (i : Fin 271) :
    original coins (order (coinIndex i))=coins i := by
  simpa [original] using updates_at (List.finRange 271) (fun i => order (coinIndex i))
    (order.injective.comp coinIndex_injective) coins (fun _ => 0) i

theorem original_pivot (coins : Fin 271 → F) : original coins 1023=0 := by
  apply updates_off
  intro i _
  exact (coin_not_pivot i).symm

theorem low_code (coins : Fin 271 → F) (j : Fin 131) :
    codeWeight (original coins) j=if j.val=128 then coins 0 else 0 := by
  unfold codeWeight
  rw [original_pivot]
  simp only [ite_self,sub_zero]
  by_cases hj : j.val=128
  · have he : lowIndex j=coinIndex 0 := by apply Fin.ext; simpa [lowIndex,coinIndex] using hj
    rw [he,original_at,if_pos hj]
  · rw [if_neg hj]
    apply updates_off
    intro i _ h
    have he := congrArg Fin.val (order.injective h)
    have hb := j.isLt
    simp only [lowIndex,coinIndex] at he
    omega

theorem point_weight (coins : Fin 271 → F) (half a b c : F) (r : Fin 128) :
    pointWeight half a b c (original coins) r=
      coins 0*ResidualModel.chordEntry half a b c r.val 128 := by
  have he (j : Fin 131) : j.val=128 ↔ j=128 := by
    constructor
    · exact fun h => Fin.ext h
    · intro h; subst j; rfl
  simp [pointWeight,low_code,he,ite_mul]

#print axioms updates_at
#print axioms updates_off
#print axioms coinIndex_injective
#print axioms original_at
#print axioms original_pivot
#print axioms low_code
#print axioms point_weight
end
end AspisR19.SparseGScatter
