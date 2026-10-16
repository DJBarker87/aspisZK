import CanonicalRawTrace
import PartialAddressImage

/-! Deterministic reuse of the legacy padded-address decoder on an
unrestricted byte trace. The legacy table defines only canonical addresses;
oversized raw queries are omitted and padding aliases remain undefined.
Every bounded canonical query and its first-read table are preserved. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawBoundedTrace

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames
open CanonicalAddressEmbedding

def canonicalDecode (L : Nat) (a : Addr L) : Option (AddrC L) := by
  classical
  exact if h : CanonicalByteAddress.Canonical a then some ⟨a,h⟩ else none

theorem canonicalDecode_iff (L : Nat) (a : Addr L) (b : AddrC L) :
    canonicalDecode L a = some b ↔ b.val = a := by
  classical
  by_cases h : CanonicalByteAddress.Canonical a
  · simp only [canonicalDecode, dif_pos h, Option.some.injEq]
    constructor
    · intro he
      exact (congrArg Subtype.val he).symm
    · intro he
      exact Subtype.ext he.symm
  · simp only [canonicalDecode, dif_neg h]
    constructor
    · intro he; cases he
    · intro he
      have hb : CanonicalByteAddress.Canonical a := he ▸ b.property
      exact False.elim (h hb)

def boundedEmbedding (L : Nat) : PartialAddressTrace.Embedding (Addr L) (AddrC L) where
  embed := Subtype.val
  decode := canonicalDecode L
  decode_iff := canonicalDecode_iff L

def trace (L : Nat) {A : Type} (tr : List (Bytes × A)) : List (Addr L × A) :=
  (boundedEmbedding L).imageTrace (CanonicalRawTrace.trace L tr)

def table (L : Nat) {A : Type} (T : Table Bytes A) : Table (Addr L) A :=
  (boundedEmbedding L).push (fun a : AddrC L => T (toBytes a))

theorem table_canonical (L : Nat) {A : Type} (T : Table Bytes A)
    (a : Addr L) (ha : CanonicalByteAddress.Canonical a) :
    table L T a = T a.toBytes :=
  (boundedEmbedding L).push_embed _ ⟨a,ha⟩

theorem table_noncanonical (L : Nat) {A : Type} (T : Table Bytes A)
    (a : Addr L) (ha : ¬ CanonicalByteAddress.Canonical a) :
    table L T a = none := by
  simp [table, PartialAddressTrace.Embedding.push, boundedEmbedding, canonicalDecode, ha]

theorem table_empty (L : Nat) {A : Type} :
    table L (emptyTable : Table Bytes A) = emptyTable :=
  (boundedEmbedding L).push_empty

theorem tableBefore_trace (L : Nat) {A : Type} (T : Table Bytes A)
    (tr : List (Bytes × A)) (a : AddrC L) :
    tableBefore (table L T) (trace L tr) a.val =
      table L (tableBefore T tr (toBytes a)) := by
  change tableBefore ((boundedEmbedding L).push (fun b : AddrC L => T (toBytes b)))
      ((boundedEmbedding L).imageTrace (CanonicalRawTrace.trace L tr))
      ((boundedEmbedding L).embed a) = _
  rw [(boundedEmbedding L).tableBefore_imageTrace]
  exact congrArg (boundedEmbedding L).push (CanonicalRawTrace.tableBefore_trace L T tr a)

theorem traceFrom_trace (L : Nat) {A : Type}
    (tr : List (Bytes × A)) (a : AddrC L) :
    traceFrom (trace L tr) a.val = trace L (traceFrom tr (toBytes a)) := by
  change traceFrom ((boundedEmbedding L).imageTrace (CanonicalRawTrace.trace L tr))
      ((boundedEmbedding L).embed a) = _
  rw [(boundedEmbedding L).traceFrom_imageTrace]
  exact congrArg (boundedEmbedding L).imageTrace
    (CanonicalRawTrace.traceFrom_trace L tr a).symm

theorem firstReads_trace_le (L : Nat) {A : Type} (tr : List (Bytes × A)) :
    firstReads emptyTable (trace L tr) ≤ firstReads emptyTable tr := by
  rw [← (boundedEmbedding L).push_empty]
  change firstReads ((boundedEmbedding L).push emptyTable)
      ((boundedEmbedding L).imageTrace (CanonicalRawTrace.trace L tr)) ≤ _
  rw [(boundedEmbedding L).firstReads_imageTrace]
  exact CanonicalRawTrace.firstReads_trace_le L tr

theorem mem_trace (L : Nat) {A : Type} (tr : List (Bytes × A))
    (a : Addr L) (v : A) :
    (a,v) ∈ trace L tr ↔
      CanonicalByteAddress.Canonical a ∧ (a.toBytes,v) ∈ tr := by
  rw [trace, (boundedEmbedding L).mem_imageTrace]
  constructor
  · rintro ⟨b, he, hmem⟩
    change b.val = a at he
    subst a
    exact ⟨b.property, (CanonicalRawTrace.mem_trace L tr b v).1 hmem⟩
  · rintro ⟨ha, hmem⟩
    exact ⟨⟨a,ha⟩, rfl, (CanonicalRawTrace.mem_trace L tr ⟨a,ha⟩ v).2 hmem⟩

theorem trace_consistent (L : Nat) {A : Type} (H : Bytes → A)
    (tr : List (Bytes × A)) (hcons : ∀ q ∈ tr, q.2 = H q.1) :
    ∀ q ∈ trace L tr, q.2 = H q.1.toBytes := by
  intro q hq
  exact hcons (q.1.toBytes,q.2) ((mem_trace L tr q.1 q.2).1 hq).2

#print axioms canonicalDecode_iff
#print axioms table_canonical
#print axioms table_noncanonical
#print axioms tableBefore_trace
#print axioms traceFrom_trace
#print axioms firstReads_trace_le
#print axioms mem_trace
#print axioms trace_consistent
end AspisR1.RawBoundedTrace
end
