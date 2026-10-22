import Stage2ContinuationTypes
import ExtractedRecordByteCanonicality

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4ReaderEActualWideCanonicalV1

open AspisR1Stage2
open AspisR1.ExtractedRecordByteCanonicality

abbrev CurrentWide := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev RecordWide := AspisR1RecordParser.field.wide_exact.WideExact
abbrev Reader := AspisR1Stage2.verifier.Reader

def currentOfRecordQM (q : AspisR1RecordParser.field.QM31) : AspisR1Stage2.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def currentOfRecordWide (w : RecordWide) : CurrentWide :=
  ⟨currentOfRecordQM w.c0, currentOfRecordQM w.c1⟩

def currentWideCanonical (w : CurrentWide) : Prop :=
  w.c0.c0.a.val < 2147483647 ∧ w.c0.c0.b.val < 2147483647 ∧
  w.c0.c1.a.val < 2147483647 ∧ w.c0.c1.b.val < 2147483647 ∧
  w.c1.c0.a.val < 2147483647 ∧ w.c1.c0.b.val < 2147483647 ∧
  w.c1.c1.a.val < 2147483647 ∧ w.c1.c1.b.val < 2147483647

private def mapRecordDecoder (r : Result (Option RecordWide)) : Result (Option CurrentWide) :=
  match r with
  | .ok o => .ok (o.map currentOfRecordWide)
  | .fail e => .fail e
  | .div => .div

/-- Concrete decoder adapter for the exact generated Reader.e call site. It
uses the retained RecordParser decoder, with only its nominal output carrier
reconstructed fieldwise into the current Stage2 WideExact type. -/
def actualCurrentWideDecoder (bytes : Slice Std.U8) : Result (Option CurrentWide) :=
  mapRecordDecoder (AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes)

theorem actualCurrentWideDecoder_success_canonical
    (bytes : Slice Std.U8) (w : CurrentWide)
    (h : actualCurrentWideDecoder bytes = .ok (some w)) : currentWideCanonical w := by
  unfold actualCurrentWideDecoder mapRecordDecoder at h
  cases hd : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes with
  | fail e => simp [hd] at h
  | div => simp [hd] at h
  | ok o =>
      cases o with
      | none => simp [hd] at h
      | some w0 =>
          simp only [hd, Option.map_some, Result.ok.injEq, Option.some.injEq] at h
          subst w
          obtain ⟨_, arr, _, hlimbs, hw⟩ :=
            AspisR1.ExtractedRecordByteCanonicality.slice_success bytes w0 hd
          subst w0
          have h0 := hlimbs (⟨0, by decide⟩ : Fin 8)
          have h1 := hlimbs (⟨1, by decide⟩ : Fin 8)
          have h2 := hlimbs (⟨2, by decide⟩ : Fin 8)
          have h3 := hlimbs (⟨3, by decide⟩ : Fin 8)
          have h4 := hlimbs (⟨4, by decide⟩ : Fin 8)
          have h5 := hlimbs (⟨5, by decide⟩ : Fin 8)
          have h6 := hlimbs (⟨6, by decide⟩ : Fin 8)
          have h7 := hlimbs (⟨7, by decide⟩ : Fin 8)
          simpa [currentWideCanonical, currentOfRecordWide, currentOfRecordQM,
            AspisR1.ExtractedRecordLimbCanonicality.packed] using
            (show (wordLE arr 0).val < 2147483647 ∧ (wordLE arr 1).val < 2147483647 ∧
              (wordLE arr 2).val < 2147483647 ∧ (wordLE arr 3).val < 2147483647 ∧
              (wordLE arr 4).val < 2147483647 ∧ (wordLE arr 5).val < 2147483647 ∧
              (wordLE arr 6).val < 2147483647 ∧ (wordLE arr 7).val < 2147483647 from
              ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩)


private theorem bind_success_local {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- The source Reader.e operation cut, with the generated decoder callee
replaced by the concrete current-carrier adapter above. Its raw-read
operation remains an explicit argument; decoder success/canonicality does not. -/
private def optionOkOr (o : Option CurrentWide) (err : verifier.Error) :
    Result (core.result.Result CurrentWide verifier.Error) :=
  match o with
  | none => .ok (.Err err)
  | some w => .ok (.Ok w)

def readerE (raw : (n : Usize) → Reader → Result (Array Std.U8 n × Reader))
    (self : Reader) : Result (core.result.Result CurrentWide verifier.Error × Reader) := do
  let (a, self1) ← raw 32#usize self
  let s ← lift (Array.to_slice a)
  let o ← actualCurrentWideDecoder s
  let r ← optionOkOr o verifier.Error.Checkpoint
  ok (r, self1)

theorem readerE_success_canonical
    (raw : (n : Usize) → Reader → Result (Array Std.U8 n × Reader))
    (r : Reader) (w : CurrentWide) (r1 : Reader)
    (h : readerE raw r = .ok (.Ok w, r1)) : currentWideCanonical w := by
  unfold readerE at h
  obtain ⟨pair, hraw, h⟩ := bind_success_local _ _ _ h
  rcases pair with ⟨bytes,r0⟩
  simp only [lift, bind_tc_ok] at h
  obtain ⟨o, hdecode, h⟩ := bind_success_local _ _ _ h
  cases o with
  | none =>
      simp only [optionOkOr, bind_tc_ok] at h
      cases h
  | some value =>
      simp only [optionOkOr, bind_tc_ok] at h
      injection h with hpair
      injection hpair with hvalue hr
      have hw : value = w := by injection hvalue
      subst w
      exact actualCurrentWideDecoder_success_canonical bytes.to_slice value hdecode

#print axioms actualCurrentWideDecoder_success_canonical
#print axioms readerE_success_canonical

end AspisR1S4ReaderEActualWideCanonicalV1
