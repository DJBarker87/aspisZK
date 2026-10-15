import R1SelectedPrefixRead
import R1CircleRecordCodec
import R1OpeningRecordCodec

/-! Staged strict reads for the selected message rows that precede each
challenge. The stages contain no challenges, words, or acceptance predicate. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedOpeningStages

open AspisR1.InitialWalk
open AspisR1.SelectedPrefixRead
open AspisR1.CircleRecordCodec
open AspisR1.OpeningRecordCodec

structure Gamma where
  row25 : CircleRecordCodec.Payload 0
  row26 : CircleRecordCodec.Payload 1
  row27 : OpeningRecordCodec.Payload .gamma

structure Kappa extends Gamma where
  row28 : OpeningRecordCodec.Payload .kappa

structure First extends Kappa where
  row29 : OpeningRecordCodec.Payload .first

structure Second extends First where
  row30 : OpeningRecordCodec.Payload .second

def readGamma (rs : List RawRec) : Option Gamma := do
  let row25 ← readAt rs 25 (CircleRecordCodec.decode 0)
  let row26 ← readAt rs 26 (CircleRecordCodec.decode 1)
  let row27 ← readAt rs 27 (OpeningRecordCodec.decode .gamma)
  pure ⟨row25, row26, row27⟩

def readKappa (rs : List RawRec) : Option Kappa := do
  let gamma ← readGamma rs
  let row28 ← readAt rs 28 (OpeningRecordCodec.decode .kappa)
  pure ⟨gamma, row28⟩

def readFirst (rs : List RawRec) : Option First := do
  let kappa ← readKappa rs
  let row29 ← readAt rs 29 (OpeningRecordCodec.decode .first)
  pure ⟨kappa, row29⟩

def readSecond (rs : List RawRec) : Option Second := do
  let first ← readFirst rs
  let row30 ← readAt rs 30 (OpeningRecordCodec.decode .second)
  pure ⟨first, row30⟩

theorem readGamma_append_stable (rs tail : List RawRec)
    (h : 27 < rs.length) : readGamma (rs ++ tail) = readGamma rs := by
  unfold readGamma
  rw [readAt_append_stable rs tail 25 _ (by omega),
      readAt_append_stable rs tail 26 _ (by omega),
      readAt_append_stable rs tail 27 _ h]

theorem readKappa_append_stable (rs tail : List RawRec)
    (h : 28 < rs.length) : readKappa (rs ++ tail) = readKappa rs := by
  unfold readKappa
  rw [readGamma_append_stable rs tail (by omega),
      readAt_append_stable rs tail 28 _ h]

theorem readFirst_append_stable (rs tail : List RawRec)
    (h : 29 < rs.length) : readFirst (rs ++ tail) = readFirst rs := by
  unfold readFirst
  rw [readKappa_append_stable rs tail (by omega),
      readAt_append_stable rs tail 29 _ h]

theorem readSecond_append_stable (rs tail : List RawRec)
    (h : 30 < rs.length) : readSecond (rs ++ tail) = readSecond rs := by
  unfold readSecond
  rw [readFirst_append_stable rs tail (by omega),
      readAt_append_stable rs tail 30 _ h]

#print axioms readGamma_append_stable
#print axioms readKappa_append_stable
#print axioms readFirst_append_stable
#print axioms readSecond_append_stable

end AspisR1.SelectedOpeningStages
end
