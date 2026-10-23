import Stage2ContinuationTypes
import AspisR1DecodeKFullParserCanonicalityCMQ
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ReaderKActualQMCanonicalV1
open AspisR1Stage2
abbrev K := aspis_core.field.QM31
abbrev AK := AspisR1DecodeKFullV10.aspis_core.field.QM31
abbrev Reader := verifier.Reader

def Canonical (q : K) : Prop :=
  q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
  q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647

def toCurrent (q : AK) : K := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
private def mapDecoder : Result (Option AK) → Result (Option K)
  | .ok o => .ok (o.map toCurrent)
  | .fail e => .fail e
  | .div => .div

/-- Reuses the proved full sixteen-byte QM decoder for checkpoint Reader.k.
This is distinct from the compact proof-buffer encoding. -/
def checkpointQMDecoder (bytes : Slice U8) : Result (Option K) :=
  mapDecoder (AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes)

theorem checkpointQMDecoder_success_canonical (bytes : Slice U8) (q : K)
    (h : checkpointQMDecoder bytes = .ok (some q)) : Canonical q := by
  unfold checkpointQMDecoder mapDecoder at h
  cases hd : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes with
  | fail e => simp [hd] at h
  | div => simp [hd] at h
  | ok o =>
    cases o with
    | none => simp [hd] at h
    | some q0 =>
      simp only [hd,Option.map_some,Result.ok.injEq,Option.some.injEq] at h
      cases h
      have hc := AspisR1DecodeKFullParserCanonicality.qm31_from_le_bytes_success_canonical
        bytes q0 hd
      have hp : AspisR1DecodeKFullV10.aspis_core.field.P.val = 2147483647 := by
        unfold AspisR1DecodeKFullV10.aspis_core.field.P
        rfl
      simpa only [Canonical,toCurrent,hp] using hc

private theorem bind_success {A B : Type} (r : Result A) (k : A → Result B) (b : B)
    (h : (do let a ← r; k a) = .ok b) : ∃ a, r = .ok a ∧ k a = .ok b := by
  cases r with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩

private def optionOkOr (o : Option K) : Result (core.result.Result K verifier.Error) :=
  match o with
  | none => .ok (.Err verifier.Error.Checkpoint)
  | some q => .ok (.Ok q)

/-- Current checkpoint Reader.k operation shape, with its fixed 16-byte
raw read and the concrete retained decoder. Raw reading and current Rust
callee/source correspondence remain explicit refinement boundaries. -/
def readerK (raw : (n : Usize) → Reader → Result (Array U8 n × Reader))
    (r : Reader) : Result (core.result.Result K verifier.Error × Reader) := do
  let (bytes,r1) ← raw 16#usize r
  let s ← lift (Array.to_slice bytes)
  let o ← checkpointQMDecoder s
  let q ← optionOkOr o
  ok (q,r1)

theorem readerK_success_canonical
    (raw : (n : Usize) → Reader → Result (Array U8 n × Reader))
    (r r1 : Reader) (q : K)
    (h : readerK raw r = .ok (.Ok q,r1)) : Canonical q := by
  unfold readerK at h
  obtain ⟨pair,hraw,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨bytes,r0⟩
  simp only [lift,bind_tc_ok] at h
  obtain ⟨o,hdecode,h⟩ := bind_success _ _ _ h
  cases o with
  | none => simp only [optionOkOr,bind_tc_ok] at h; cases h
  | some value =>
    simp only [optionOkOr,bind_tc_ok] at h
    injection h with hp
    injection hp with hv hr
    have he : value = q := by injection hv
    subst q
    exact checkpointQMDecoder_success_canonical bytes.to_slice value hdecode

#print axioms checkpointQMDecoder_success_canonical
#print axioms readerK_success_canonical
end AspisR1S9ReaderKActualQMCanonicalV1
