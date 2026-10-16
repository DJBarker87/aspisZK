import PartialAddressTrace
import R1CanonicalAddressEmbedding

/-! Restrict unrestricted raw-byte oracle traces to canonical padded
addresses without ever sending an oversized input to a fallback address.
This is a deterministic decoder-reuse bridge, not a restriction on the
adversary's inputs or a transport of the random-oracle probability law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.CanonicalRawTrace

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames
open CanonicalAddressEmbedding

def decode (L : Nat) (input : Bytes) : Option (AddrC L) :=
  if h : input.length ≤ L then
    some ⟨Addr.ofBytes input h, CanonicalByteAddress.canonical_ofBytes input h⟩
  else none

theorem decode_iff (L : Nat) (input : Bytes) (a : AddrC L) :
    decode L input = some a ↔ toBytes a = input := by
  by_cases h : input.length ≤ L
  · simp only [decode, dif_pos h, Option.some.injEq]
    constructor
    · intro he
      rw [← he]
      exact Addr.toBytes_ofBytes input h
    · intro he
      apply toBytes_injective
      exact (Addr.toBytes_ofBytes input h).trans he.symm
  · simp only [decode, dif_neg h]
    constructor
    · intro he
      cases he
    · intro he
      exact False.elim (h (by rw [← he]; exact image_length_le a))

def embedding (L : Nat) : PartialAddressTrace.Embedding Bytes (AddrC L) where
  embed := toBytes
  decode := decode L
  decode_iff := decode_iff L

theorem decode_oversized (L : Nat) (input : Bytes) (h : L < input.length) :
    decode L input = none := by
  simp [decode, Nat.not_le_of_lt h]

theorem decode_canonical (L : Nat) (a : AddrC L) :
    decode L (toBytes a) = some a := (decode_iff L _ a).2 rfl

def trace (L : Nat) {A : Type} (tr : List (Bytes × A)) : List (AddrC L × A) :=
  (embedding L).project tr

theorem tableBefore_trace (L : Nat) {A : Type} (T : Table Bytes A)
    (tr : List (Bytes × A)) (a : AddrC L) :
    tableBefore (fun b : AddrC L => T (toBytes b)) (trace L tr) a =
      fun b : AddrC L => tableBefore T tr (toBytes a) (toBytes b) :=
  (embedding L).tableBefore_project T tr a

theorem traceFrom_trace (L : Nat) {A : Type}
    (tr : List (Bytes × A)) (a : AddrC L) :
    trace L (traceFrom tr (toBytes a)) = traceFrom (trace L tr) a :=
  (embedding L).traceFrom_project tr a

theorem firstReads_trace_le (L : Nat) {A : Type} (tr : List (Bytes × A)) :
    firstReads emptyTable (trace L tr) ≤ firstReads emptyTable tr :=
  (embedding L).firstReads_project_le emptyTable tr

theorem mem_trace (L : Nat) {A : Type} (tr : List (Bytes × A))
    (a : AddrC L) (v : A) :
    (a,v) ∈ trace L tr ↔ (toBytes a,v) ∈ tr :=
  (embedding L).mem_project tr a v

#print axioms decode_iff
#print axioms decode_oversized
#print axioms tableBefore_trace
#print axioms traceFrom_trace
#print axioms firstReads_trace_le
#print axioms mem_trace
end AspisR1.CanonicalRawTrace
end
