import Mathlib.Tactic

/-! A row-indexed parser for already delimited records. The payload type may
depend on the row, without adding an artificial row tag to the encoded bytes.
This supplies prefix laws only; the concrete semantic/opening decoders and
their correspondence with verifier bytes remain separate obligations. -/
set_option autoImplicit false
namespace AspisR1.TypedPrefixParser

variable {Raw : Type} {Payload : Nat → Type}

def decode (one : (row : Nat) → Raw → Option (Payload row)) :
    Nat → List Raw → Option (List (Sigma Payload))
  | _, [] => some []
  | row, raw :: rest => do
      let value ← one row raw
      let tail ← decode one (row + 1) rest
      pure (⟨row, value⟩ :: tail)

theorem decode_append (one : (row : Nat) → Raw → Option (Payload row))
    (row : Nat) (preRaw suffix : List Raw) :
    decode one row (preRaw ++ suffix) =
      (decode one row preRaw).bind (fun pre =>
        (decode one (row + preRaw.length) suffix).map (fun post => pre ++ post)) := by
  induction preRaw generalizing row with
  | nil => simp [decode]
  | cons raw rest ih =>
      cases hfirst : one row raw with
      | none => simp [decode, hfirst]
      | some value =>
          rw [List.cons_append]
          simp only [decode, hfirst]
          rw [ih]
          cases hrest : decode one (row + 1) rest <;>
            simp [Nat.add_comm, Nat.add_left_comm]
          cases decode one (row + (rest.length + 1)) suffix <;> rfl

theorem decode_length (one : (row : Nat) → Raw → Option (Payload row))
    (row : Nat) (raws : List Raw) (out : List (Sigma Payload))
    (h : decode one row raws = some out) : out.length = raws.length := by
  induction raws generalizing row out with
  | nil =>
      have hout : ([] : List (Sigma Payload)) = out := by simpa [decode] using h
      rw [← hout]
      rfl
  | cons raw rest ih =>
      cases hfirst : one row raw with
      | none => simp [decode, hfirst] at h
      | some value =>
          cases hrest : decode one (row + 1) rest with
          | none => simp [decode, hfirst, hrest] at h
          | some tail =>
              have hout : (⟨row, value⟩ :: tail) = out := by
                simpa [decode, hfirst, hrest] using h
              rw [← hout]
              simpa using congrArg Nat.succ (ih (row + 1) tail hrest)

theorem decode_rows (one : (row : Nat) → Raw → Option (Payload row))
    (row : Nat) (raws : List Raw) (out : List (Sigma Payload))
    (h : decode one row raws = some out) :
    out.map Sigma.fst = List.range' row raws.length := by
  induction raws generalizing row out with
  | nil =>
      have hout : ([] : List (Sigma Payload)) = out := by simpa [decode] using h
      rw [← hout]
      rfl
  | cons raw rest ih =>
      cases hfirst : one row raw with
      | none => simp [decode, hfirst] at h
      | some value =>
          cases hrest : decode one (row + 1) rest with
          | none => simp [decode, hfirst, hrest] at h
          | some tail =>
              have hout : (⟨row, value⟩ :: tail) = out := by
                simpa [decode, hfirst, hrest] using h
              rw [← hout, List.map_cons, List.length_cons, List.range'_succ]
              exact congrArg (List.cons row) (ih (row + 1) tail hrest)

theorem decode_append_some (one : (row : Nat) → Raw → Option (Payload row))
    (row : Nat) (preRaw suffix : List Raw) (out : List (Sigma Payload))
    (h : decode one row (preRaw ++ suffix) = some out) :
    ∃ pre post, decode one row preRaw = some pre ∧
      decode one (row + preRaw.length) suffix = some post ∧ out = pre ++ post := by
  rw [decode_append] at h
  cases hp : decode one row preRaw with
  | none => simp [hp] at h
  | some pre =>
      cases hs : decode one (row + preRaw.length) suffix with
      | none => simp [hp, hs] at h
      | some post =>
          refine ⟨pre, post, rfl, rfl, ?_⟩
          have hout : pre ++ post = out := by simpa [hp, hs] using h
          exact hout.symm

theorem prefix_stable (one : (row : Nat) → Raw → Option (Payload row))
    (row : Nat) (preRaw suffix : List Raw) (out : List (Sigma Payload))
    (h : decode one row (preRaw ++ suffix) = some out) :
    decode one row preRaw = some (out.take preRaw.length) := by
  obtain ⟨pre, post, hp, _, hout⟩ := decode_append_some one row preRaw suffix out h
  have hlen := decode_length one row preRaw pre hp
  rw [hout, ← hlen, List.take_left]
  exact hp

theorem failure_persists (one : (row : Nat) → Raw → Option (Payload row))
    (row : Nat) (preRaw suffix : List Raw)
    (h : decode one row preRaw = none) :
    decode one row (preRaw ++ suffix) = none := by
  simp [decode_append, h]

#print axioms decode_append
#print axioms decode_length
#print axioms decode_rows
#print axioms decode_append_some
#print axioms prefix_stable
#print axioms failure_persists

end AspisR1.TypedPrefixParser
