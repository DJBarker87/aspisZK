import NPR_R22DotSite

/-! NPR_ (R22, weights.field literal sites): the deployed finish round and Horner polynomial. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPR_R22LiteralSites
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem round_congr {W : Type} (ops : Stage2Finish.FinishOps W) (f' : type_of% ops.field)
    (poly : Slice U8) (alpha claim : aspis_core.field.wide_exact.WideExact) (round : Usize)
    (h0 : f' poly 0#usize = ops.field poly 0#usize) (h4 : f' poly 4#usize = ops.field poly 4#usize) :
    Port4D_Round.round { ops with field := f' } poly alpha claim round =
      Port4D_Round.round ops poly alpha claim round := by
  unfold Port4D_Round.round
  simp only [h0, h4]

/-- The finish round calls its field slot only at the literals 0 and 4. -/
theorem round_guarded {W : Type} (ops : Stage2Finish.FinishOps W)
    (poly : Slice U8) (alpha claim : aspis_core.field.wide_exact.WideExact) (round : Usize) :
    Port4D_Round.round { ops with field := fun p i => if i.val < 64 then ops.field p i else fail .panic }
        poly alpha claim round =
      Port4D_Round.round ops poly alpha claim round :=
  round_congr ops _ poly alpha claim round (if_pos (by decide)) (if_pos (by decide))

theorem deployed_round_slots (r : NP6_StdModel.Reservation) :
    (NIG_Slots.installed r).op5 = Port4D_Round.round (Port3_FinishStage.release (IDa_Deployed.finish r)) ∧
    (Port3_FinishStage.release (IDa_Deployed.finish r)).field = FIn_Primitives.field ∧
    (Port3_FinishStage.release (IDa_Deployed.finish r)).polynomial = FIn_ExtractInstall.polynomial :=
  ⟨rfl, rfl, rfl⟩

theorem primitives_field_body (bytes : Slice U8) (i : Usize) :
    FIn_Primitives.field bytes i = (do
      let x ← AspisR1CurrentWide.Proof.finishField bytes i
      ok (SAG_DotAdapter.toStageE x)) := rfl

/-- The deployed Horner polynomial calls its field slot only at the literals 6, 5, ..., 0. -/
theorem poly_guarded (poly : Slice U8) (x : Stage2Finish.E) :
    FIn_Extract.FIn_reference.polynomial (A := Unit)
        { FIn_ExtractInstall.arithmetic with
          field := fun p i => if i.val < 64 then FIn_ExtractInstall.arithmetic.field p i else fail .panic }
        poly x =
      FIn_ExtractInstall.polynomial poly x := by
  have g : ∀ i : Usize, i.val < 64 →
      (if i.val < 64 then FIn_ExtractInstall.arithmetic.field poly i else fail .panic) =
        FIn_ExtractInstall.arithmetic.field poly i := fun i h => if_pos h
  unfold FIn_ExtractInstall.polynomial FIn_Extract.FIn_reference.polynomial
  simp only [g 0#usize (by decide), g 1#usize (by decide), g 2#usize (by decide), g 3#usize (by decide),
    g 4#usize (by decide), g 5#usize (by decide), g 6#usize (by decide)]

theorem arithmetic_field : FIn_ExtractInstall.arithmetic.field = FIn_Primitives.field := rfl

#print axioms round_congr
#print axioms round_guarded
#print axioms deployed_round_slots
#print axioms primitives_field_body
#print axioms poly_guarded
#print axioms arithmetic_field
end AspisR1.NPR_R22LiteralSites
