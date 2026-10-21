import AspisR1CheckedQCandidateV1.Funs
import FourDotsCurrentQmParserRootV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S4QCheckedQCurrentSemanticsV1

open AspisR1.RetainedFieldByteCodec
open AspisR1FastDotsCurrentQmParserRootV1

abbrev CandidateQ := AspisR1CheckedQCandidateV1.Q
abbrev CurrentQM := AspisR1FastDotsCurrentQmParserRootV1.QM

def candidateCoord (q : CandidateQ) (i : Fin 4) : Nat :=
  (q.val[i.val]'(by
    have hlen : q.val.length = 4 := by
      simpa [UScalar.ofNatCore_val_eq] using q.property
    omega)).val

def currentCoord (q : CurrentQM) (i : Fin 4) : Nat :=
  if h : i.val = 0 then q.c0.a.val else
  if h : i.val = 1 then q.c0.b.val else
  if h : i.val = 2 then q.c1.a.val else q.c1.b.val

def sourceLimbs (q : CurrentQM) : Array Std.U32 4#usize :=
  Array.make 4#usize [q.c0.a, q.c0.b, q.c1.a, q.c1.b]

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok a => .ok (f a)
  | .fail e => .fail e
  | .div => .div

def normalizedCandidate (r : Result (Option CandidateQ)) :
    Result (Option (Fin 4 → Nat)) :=
  mapResult (Option.map fun q i => candidateCoord q i) r

theorem checked_q_source_limbs_are_canonical (q : CurrentQM)
    (h0 : q.c0.a.val < m31Modulus) (h1 : q.c0.b.val < m31Modulus)
    (h2 : q.c1.a.val < m31Modulus) (h3 : q.c1.b.val < m31Modulus) :
    AspisR1CheckedQCandidateV1.Q.from_limbs (sourceLimbs q) =
      .ok (some (sourceLimbs q)) := by
  have hi0 : Array.index_usize (sourceLimbs q) 0#usize = .ok q.c0.a := by
    simp [sourceLimbs, Array.index_usize, Array.make]
  have hi1 : Array.index_usize (sourceLimbs q) 1#usize = .ok q.c0.b := by
    simp [sourceLimbs, Array.index_usize, Array.make]
  have hi2 : Array.index_usize (sourceLimbs q) 2#usize = .ok q.c1.a := by
    simp [sourceLimbs, Array.index_usize, Array.make]
  have hi3 : Array.index_usize (sourceLimbs q) 3#usize = .ok q.c1.b := by
    simp [sourceLimbs, Array.index_usize, Array.make]
  have hp0 : q.c0.a < AspisR1CheckedQCandidateV1.P := by
    simpa [UScalar.lt_equiv, AspisR1CheckedQCandidateV1.P, m31Modulus, rawCandidateCount] using h0
  have hp1 : q.c0.b < AspisR1CheckedQCandidateV1.P := by
    simpa [UScalar.lt_equiv, AspisR1CheckedQCandidateV1.P, m31Modulus, rawCandidateCount] using h1
  have hp2 : q.c1.a < AspisR1CheckedQCandidateV1.P := by
    simpa [UScalar.lt_equiv, AspisR1CheckedQCandidateV1.P, m31Modulus, rawCandidateCount] using h2
  have hp3 : q.c1.b < AspisR1CheckedQCandidateV1.P := by
    simpa [UScalar.lt_equiv, AspisR1CheckedQCandidateV1.P, m31Modulus, rawCandidateCount] using h3
  unfold AspisR1CheckedQCandidateV1.Q.from_limbs
  rw [hi0, hi1, hi2, hi3]
  simp only [bind_tc_ok]
  simp [hp0, hp1, hp2, hp3]

theorem checked_q_source_output_coordinates (q : CurrentQM)
    (h0 : q.c0.a.val < m31Modulus) (h1 : q.c0.b.val < m31Modulus)
    (h2 : q.c1.a.val < m31Modulus) (h3 : q.c1.b.val < m31Modulus) :
    normalizedCandidate
      (AspisR1CheckedQCandidateV1.Q.from_limbs (sourceLimbs q)) =
      .ok (some (currentCoord q)) := by
  rw [checked_q_source_limbs_are_canonical q h0 h1 h2 h3]
  simp only [normalizedCandidate, mapResult, Option.map_some]
  apply congrArg Result.ok
  apply congrArg some
  funext i
  fin_cases i <;> simp [candidateCoord, currentCoord, sourceLimbs, Array.make]

/-- The exact parser's successful result supplies all four canonicality facts
needed by the emitted checked_q limb validation, for the same decoded q. -/
theorem parser_success_checked_q_coordinates
    (ops : Ops) (bytes : Array U8 16#usize) (q : CurrentQM)
    (hparse : (withCurrentQmParser ops).qm31FromBytes (Array.to_slice bytes) =
      .ok (some q)) :
    normalizedCandidate
      (AspisR1CheckedQCandidateV1.Q.from_limbs (sourceLimbs q)) =
      .ok (some (currentCoord q)) := by
  obtain ⟨limbs, hdecode, hq, hencode, h0, h1, h2, h3⟩ :=
    installed_parser_success_strict ops bytes q hparse
  exact checked_q_source_output_coordinates q h0 h1 h2 h3

#print axioms checked_q_source_limbs_are_canonical
#print axioms checked_q_source_output_coordinates
#print axioms parser_success_checked_q_coordinates

end AspisR1S4QCheckedQCurrentSemanticsV1
