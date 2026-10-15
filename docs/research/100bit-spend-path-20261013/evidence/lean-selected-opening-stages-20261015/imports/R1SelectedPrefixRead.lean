import R1SelectedIndexedRead

/-! Indexed parsing of already typed raw records. This is list/read plumbing
only; no table, trace, or acceptance property is asserted. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedPrefixRead

open AspisV8R19.DuplexFrames
open AspisR1.InitialWalk
open AspisR1.SelectedTranscriptParams

def readAt {A : Type} (rs : List InitialWalk.RawRec) (i : Nat)
    (d : Bytes → Option A) : Option A :=
  (rs[i]?).bind fun r =>
    SelectedIndexedRead.readTyped i r.label r.data d

theorem readAt_append_stable {A : Type} (rs tail : List InitialWalk.RawRec)
    (i : Nat) (d : Bytes → Option A) (hi : i < rs.length) :
    readAt (rs ++ tail) i d = readAt rs i d := by
  unfold readAt
  rw [List.getElem?_append_left hi]

theorem readAt_sound {A : Type} (rs : List InitialWalk.RawRec) (i : Nat)
    (d : Bytes → Option A) (a : A) (h : readAt rs i d = some a) :
    ∃ r, rs[i]? = some r ∧
      r.label = SelectedTranscriptParams.params.lbl i ∧ d r.data = some a := by
  unfold readAt at h
  rcases Option.bind_eq_some_iff.mp h with ⟨r, hindex, hread⟩
  have hs := SelectedIndexedRead.readTyped_sound i r.label r.data d a hread
  exact ⟨r, hindex, hs.1, hs.2⟩

#print axioms readAt_append_stable
#print axioms readAt_sound

end AspisR1.SelectedPrefixRead
end
