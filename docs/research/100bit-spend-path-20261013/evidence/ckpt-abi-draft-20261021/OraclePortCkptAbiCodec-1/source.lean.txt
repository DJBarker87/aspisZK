import OraclePortCheckpointOracleC5

/-! Saved-ten reference codec. This is a total Option function, including
repeated-query rejection. It is not an identification with extracted Rust. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCkptAbiCodec
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OraclePortCheckpointStateC3.advance
  OraclePortCheckpointStateC3.write QueryAccumulator.run QueryAccumulator.run22

abbrev Decoded := Prepared × QueryAccumulator.State K E

def decode (ck : Bytes) : Option Decoded := do
  let p ← OraclePortCheckpointPreparedC5.decode ck
  if Function.Injective p.queries then
    let a ← decodeAccumulator ck
    pure (p,a)
  else none

/-- Exact total result on every typed saved-ten encoder input. Distinctness is
part of the result, not an unproved premise silently inherited from C5. -/
theorem decode_encode (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) (next : a.next = 10) :
    decode (encode H stored pub p a) =
      if Function.Injective p.queries then some (p,a) else none := by
  simp only [decode,OraclePortCheckpointPreparedC5.decode_encode,
    Option.bind_eq_bind,Option.bind_some]
  split
  · rw [decode_written H stored pub p a next]; rfl
  · rfl

/-- Every prepared component and every accumulator component is returned
from the physical slices; digests remain explicitly authenticated separately. -/
theorem saved_fields (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    decode (save H stored pub c d rho q).checkpoint =
      if Function.Injective q then
        some (prepared c d rho q,
          (OraclePortCheckpointStateC3.write (model d rho q)).accumulator)
      else none :=
  decode_encode H stored pub _ _ (OraclePortCheckpointStateC3.saved_next _)

/-- A repeated query gives a concrete obstruction to unconditional successful
Rust roundtrip on all C5 Prepared values. No large finite universe is reduced. -/
theorem repeated_query_rejected (H : Bytes → State) (stored pub : Bytes)
    (p : Prepared) (a : QueryAccumulator.State K E) (next : a.next = 10)
    (i j : Fin 22) (different : i ≠ j) (same : p.queries i = p.queries j) :
    decode (encode H stored pub p a) = none := by
  rw [decode_encode H stored pub p a next]
  exact if_neg (fun injective => different (injective same))

/-- Full save result: retained proof, exact length, prepared state, saved-ten
accumulator and all three digest bindings. No checksum-forgery inference. -/
theorem save_contract (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144)
    (unique : Function.Injective q) :
    (save H stored pub c d rho q).stored = stored ∧
    HashBinding H pub (save H stored pub c d rho q) ∧
    decode (save H stored pub c d rho q).checkpoint =
      some (prepared c d rho q,
        (OraclePortCheckpointStateC3.write (model d rho q)).accumulator) := by
  refine ⟨rfl,save_hash_binding H stored pub c d rho q,?_⟩
  rw [saved_fields,if_pos unique]

#print axioms decode_encode
#print axioms saved_fields
#print axioms repeated_query_rejected
#print axioms save_contract
end AspisR1.OraclePortCkptAbiCodec
end
