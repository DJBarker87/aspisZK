import R1SelectedOpeningData
import R1SelectedPrefixRead

/-! Read the seven selected circle/opening records from an already typed
record list. This is indexed parsing only; it makes no acceptance or trace
claim. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.SelectedOpeningRead

open AspisR1.CircleRecordCodec
open AspisR1.OpeningRecordCodec
open AspisR1.SelectedOpeningData
open AspisR1.SelectedPrefixRead
open AspisR1.SelectedTranscriptParams

/-- Decode the selected records at rows 25 through 31. -/
def read (rs : List InitialWalk.RawRec) : Option SelectedOpeningData.Payloads := do
  let row25 ← readAt rs 25 (CircleRecordCodec.decode 0)
  let row26 ← readAt rs 26 (CircleRecordCodec.decode 1)
  let row27 ← readAt rs 27 (OpeningRecordCodec.decode .gamma)
  let row28 ← readAt rs 28 (OpeningRecordCodec.decode .kappa)
  let row29 ← readAt rs 29 (OpeningRecordCodec.decode .first)
  let row30 ← readAt rs 30 (OpeningRecordCodec.decode .second)
  let row31 ← readAt rs 31 (OpeningRecordCodec.decode .final)
  pure ⟨row25, row26, row27, row28, row29, row30, row31⟩

/-- The seven successful indexed reads represented by `read`. -/
def Reads (rs : List InitialWalk.RawRec) (p : SelectedOpeningData.Payloads) : Prop :=
  readAt rs 25 (CircleRecordCodec.decode 0) = some p.row25 ∧
  readAt rs 26 (CircleRecordCodec.decode 1) = some p.row26 ∧
  readAt rs 27 (OpeningRecordCodec.decode .gamma) = some p.row27 ∧
  readAt rs 28 (OpeningRecordCodec.decode .kappa) = some p.row28 ∧
  readAt rs 29 (OpeningRecordCodec.decode .first) = some p.row29 ∧
  readAt rs 30 (OpeningRecordCodec.decode .second) = some p.row30 ∧
  readAt rs 31 (OpeningRecordCodec.decode .final) = some p.row31

theorem read_eq_some_iff (rs : List InitialWalk.RawRec)
    (p : SelectedOpeningData.Payloads) :
    read rs = some p ↔ Reads rs p := by
  constructor
  · intro h
    unfold read at h
    simp only [Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    rcases h with ⟨v25, h25, v26, h26, v27, h27, v28, h28,
      v29, h29, v30, h30, v31, h31, hp⟩
    have heq : (⟨v25, v26, v27, v28, v29, v30, v31⟩ : SelectedOpeningData.Payloads) = p := hp
    cases heq
    simp only [Reads]
    constructor
    · exact h25
    constructor
    · exact h26
    constructor
    · exact h27
    constructor
    · exact h28
    constructor
    · exact h29
    constructor
    · exact h30
    · exact h31
  · intro h
    rcases h with ⟨h25, h26, h27, h28, h29, h30, h31⟩
    unfold read
    simp [h25, h26, h27, h28, h29, h30, h31]

theorem read_append_stable (rs tail : List InitialWalk.RawRec)
    (h : 31 < rs.length) :
    read (rs ++ tail) = read rs := by
  unfold read
  rw [readAt_append_stable rs tail 25 _ (by omega)]
  rw [readAt_append_stable rs tail 26 _ (by omega)]
  rw [readAt_append_stable rs tail 27 _ (by omega)]
  rw [readAt_append_stable rs tail 28 _ (by omega)]
  rw [readAt_append_stable rs tail 29 _ (by omega)]
  rw [readAt_append_stable rs tail 30 _ (by omega)]
  rw [readAt_append_stable rs tail 31 _ h]

#print axioms read_eq_some_iff
#print axioms read_append_stable

end AspisR1.SelectedOpeningRead

end
