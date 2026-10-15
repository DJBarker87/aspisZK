import R1LiteralTranscript
import AspisV8R19.R412LegalQueryEnumeration

/-! A strict, ordered projection for a successful q22 result carried in a
literal transcript challenge. This is list-model plumbing only: it does not
prove validity of the sampler's selected scan result or connect to source
execution. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralQueryRead

open AspisR1.LiteralTranscript
open AspisR1.TranscriptView
open AspisV8R19.R412LegalQueryEnumeration

/-- Accept exactly a duplicate-free, bounded query list of length 22, and
retain its original order as a coordinate function. -/
def decode (xs : List Nat) : Option (Fin 22 → Fin 262144) :=
  if h : xs.Nodup ∧ xs.length = 22 ∧ ∀ x ∈ xs, x < 262144 then
    some (legalOfList xs h.1 h.2.1 h.2.2).val
  else none

/-- Read a query challenge only at an indexed literal transcript entry. Errors,
ordinary challenges, malformed query lists, and out-of-range indices fail. -/
def queriesAt (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) : Option (Fin 22 → Fin 262144) :=
  rs[i]?.bind fun mc =>
    match mc.2.1 with
    | Value.queries (.ok xs) => decode xs
    | _ => none

theorem queriesAt_append
    (rs tail : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) (hi : i < rs.length) :
    queriesAt (rs ++ tail) i = queriesAt rs i := by
  simp only [queriesAt, List.getElem?_append_left hi]

/-- A successful decode returns the original list in coordinate order and an
injective coordinate function. -/
theorem decode_success (xs : List Nat) (q : Fin 22 → Fin 262144)
    (hdecode : decode xs = some q) :
    List.ofFn (fun j : Fin 22 => (q j).val) = xs ∧ Function.Injective q := by
  unfold decode at hdecode
  split_ifs at hdecode with hvalid
  · simp only [Option.some.injEq] at hdecode
    subst q
    have henum := enum_legalOfList xs hvalid.1 hvalid.2.1 hvalid.2.2
    have hq : Function.Injective
        (legalOfList xs hvalid.1 hvalid.2.1 hvalid.2.2).val :=
      (legalOfList xs hvalid.1 hvalid.2.1 hvalid.2.2).property
    constructor
    · simpa only [enumQuery] using henum
    · exact hq

#print axioms queriesAt_append
#print axioms decode_success

end AspisR1.LiteralQueryRead
end
