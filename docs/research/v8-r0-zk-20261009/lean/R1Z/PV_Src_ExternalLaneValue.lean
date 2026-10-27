import R1Z.PV_Src_ExternalLaneCells

/-! The exact source lane has ordinary modular-add semantics under the
column-sum bound established separately from its source recurrence. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalLaneValue
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_Src_ExternalLaneStep

theorem value (s : State) (sums : Sums) (lane : Usize)
    (hs : sums.val[lane.val%4]!.val < 17179869184) :
    (cell s sums lane).val =
      (s.val[lane.val]!.val+sums.val[lane.val%4]!.val)%2147483647 := by
  unfold cell
  rw [PV_Src_ScalarReduce.modulo,
    add64v _ _ _ _ (c64 _) rfl (by have := u32lt s.val[lane.val]!;omega)]

theorem lift (s : State) (sums : Sums) (lane : Usize)
    (hs : sums.val[lane.val%4]!.val < 17179869184)
    {K : Type} [Field K] [CharP K 2147483647] :
    liftU (K := K) (cell s sums lane) =
      liftU s.val[lane.val]!+(sums.val[lane.val%4]!.val : K) := by
  unfold liftU
  rw [value s sums lane hs,cast_mod,Nat.cast_add]

#print axioms value
#print axioms lift
end R1Z.PV_Src_ExternalLaneValue
