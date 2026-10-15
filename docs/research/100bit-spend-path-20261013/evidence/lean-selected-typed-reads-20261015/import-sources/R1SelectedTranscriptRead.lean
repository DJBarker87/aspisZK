import R1SelectedSemanticRead
import R1SelectedOpeningRead

/-! Strict payload parsing at all 33 selected row positions. This model reads
already supplied raw records; challenge/table recovery and Rust refinement
are not conclusions of these statements. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedTranscriptRead

structure Payloads where
  semantic : SelectedSemanticRead.Payloads
  opening : SelectedOpeningData.Payloads
  rho : OpeningRecordCodec.Payload .rho

def read (rs : List InitialWalk.RawRec) : Option Payloads := do
  let semantic ← SelectedSemanticRead.read rs
  let opening ← SelectedOpeningRead.read rs
  let rho ← SelectedPrefixRead.readAt rs 32 (OpeningRecordCodec.decode .rho)
  pure ⟨semantic, opening, rho⟩

def Reads (rs : List InitialWalk.RawRec) (p : Payloads) : Prop :=
  SelectedSemanticRead.read rs = some p.semantic ∧
  SelectedOpeningRead.read rs = some p.opening ∧
  SelectedPrefixRead.readAt rs 32 (OpeningRecordCodec.decode .rho) = some p.rho

theorem read_eq_some_iff (rs : List InitialWalk.RawRec) (p : Payloads) :
    read rs = some p ↔ Reads rs p := by
  constructor
  · intro h
    unfold read at h
    simp only [Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    rcases h with ⟨semantic, hs, opening, ho, rho, hr, hp⟩
    cases hp
    exact ⟨hs, ho, hr⟩
  · rintro ⟨hs, ho, hr⟩
    simp [read, hs, ho, hr]

theorem read_append_stable (rs tail : List InitialWalk.RawRec)
    (h : 32 < rs.length) : read (rs ++ tail) = read rs := by
  unfold read
  rw [SelectedSemanticRead.read_append_stable rs tail (by omega),
    SelectedOpeningRead.read_append_stable rs tail (by omega),
    SelectedPrefixRead.readAt_append_stable rs tail 32 _ h]

def readExact (rs : List InitialWalk.RawRec) : Option Payloads :=
  if rs.length = 33 then read rs else none

theorem readExact_eq_some_iff (rs : List InitialWalk.RawRec) (p : Payloads) :
    readExact rs = some p ↔ rs.length = 33 ∧ Reads rs p := by
  by_cases h : rs.length = 33
  · simp [readExact, h, read_eq_some_iff]
  · simp [readExact, h]

#print axioms read_eq_some_iff
#print axioms read_append_stable
#print axioms readExact_eq_some_iff

end AspisR1.SelectedTranscriptRead
end
