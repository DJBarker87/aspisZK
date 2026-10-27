import LPi_SerializationFold
set_option autoImplicit false
namespace AspisR1.LPm_WeightLoop
open Aeneas Aeneas.Std Result OraclePortCkptAbi2Extracted
abbrev Q := aspis_core.field.QM31
abbrev Accumulator := aspis_r1_cost_probe.verifier.Accumulator

/-- The remaining shared slice, current owned Vec bytes, and final Vec bytes.
Each cons is ONE actual iterator.next / put_k transition. The native gates
identify the fetched value with the head and the restored iterator with tail;
LPi's arbitrary-prestate native put_k gate supplies the append equation. -/
inductive Trace : List Q → List U8 → List U8 → Prop where
  | done (buf : List U8) : Trace [] buf buf
  | step (x : Q) (xs : List Q) (buf next out : List U8)
      (write : next = LPi_SerializationFold.append buf x)
      (rest : Trace xs next out) : Trace (x::xs) buf out

/-- No whole-output equality is a field of Trace. It follows from the local
transitions and the existing fold theorem. -/
theorem result {xs : List Q} {buf out : List U8} (tr : Trace xs buf out) :
    out = LPi_SerializationFold.fold buf xs := by
  induction tr with
  | done buf => rfl
  | step x xs buf next out write rest ih =>
    rw [ih,write]
    rfl

/-- The local transition relation is inhabited for every remaining slice and
initial Vec, including noncanonical raw QM31 values. -/
theorem exists_trace (xs : List Q) (buf : List U8) :
    Trace xs buf (LPi_SerializationFold.fold buf xs) := by
  induction xs generalizing buf with
  | nil => exact .done buf
  | cons x xs ih =>
    exact .step x xs buf (LPi_SerializationFold.append buf x) _ rfl (ih _)

/-- Actual checkpoint Accumulator carrier, rather than a fresh chosen weight
list. The native one-step domain covers every reached 712+16*i prefix. -/
theorem native_weights (a : Accumulator) (buf out : List U8)
    (size : a.weights.val.length = 64) (prefixSize : buf.length = 712)
    (tr : Trace a.weights.val buf out) :
    out = buf ++ a.weights.val.flatMap CheckpointP6EncodeK.bytes ∧
      out.length = 1736 := by
  rw [result tr]
  exact LPi_SerializationFold.weights64 buf a.weights.val prefixSize size

theorem reached_size (buf : List U8) (weights : List Q) (i : Nat)
    (prefixSize : buf.length = 712) (size : weights.length = 64) (bound : i ≤ 64) :
    (LPi_SerializationFold.fold buf (weights.take i)).length = 712+16*i := by
  rw [LPi_SerializationFold.length,List.length_take,prefixSize,size,Nat.min_eq_left bound]

theorem reached_domain (i : Nat) (bound : i < 64) :
    712+16*i ≤ 1720 ∧ 712+16*(i+1) ≤ 1736 := by omega

#print axioms result
#print axioms exists_trace
#print axioms native_weights
#print axioms reached_size
#print axioms reached_domain
end AspisR1.LPm_WeightLoop
