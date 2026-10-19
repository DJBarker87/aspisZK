import ExtractedSourceDigestOracle
import FS2.DuplexTrace

/-! Source-observation subtrace for typed recovery: the actual initializer,
three dictionary observations from each reached Call, and the next actual
absorb. This does not identify the complete runtime/syscall583-call log. -/
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceObservations
open r1_wire SourceDigestAddresses SourceDigestOracle
open FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

abbrev Observation (L : Nat) := Addr L × State

def row {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) (c : SourceFull25.Call D pre)
    (bound : (rawBytes c.record.framed).length ≤ p.D) : List (Observation L) :=
  [(absorbA p (decodeState c.before.state) (decodeByte c.tag) (rawBytes c.record.framed) bound,
      decodeState c.absorbed),
    (squeezeA p (decodeState c.absorbed), decodeState c.block),
    (advanceA p (decodeState c.absorbed), decodeState c.after.state)]

def rows {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D) : List (Observation L) :=
  cs.attach.flatMap (fun c => row p c.val (bound c.val c.property))

def relevant {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D)
    (initial target : Observation L) : List (Observation L) :=
  initial :: (rows p cs bound ++ [target])

theorem row_length {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) (c : SourceFull25.Call D pre)
    (bound : (rawBytes c.record.framed).length ≤ p.D) : (row p c bound).length = 3 := rfl

theorem rows_length {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D) :
    (rows p cs bound).length = 3 * cs.length := by
  simp [rows, row, List.length_flatMap, Nat.mul_comm]

theorem relevant_length {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D)
    (initial target : Observation L) :
    (relevant p cs bound initial target).length = 3 * cs.length + 2 := by
  simp [relevant, rows_length] <;> omega

theorem rows_mem {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D)
    (c : SourceFull25.Call D pre) (hc : c ∈ cs) (q : Observation L)
    (hq : q ∈ row p c (bound c hc)) : q ∈ rows p cs bound := by
  apply List.mem_flatMap.mpr
  exact ⟨⟨c,hc⟩, by simp, hq⟩

theorem relevant_row_mem {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D)
    (initial target : Observation L)
    (c : SourceFull25.Call D pre) (hc : c ∈ cs) (q : Observation L)
    (hq : q ∈ row p c (bound c hc)) : q ∈ relevant p cs bound initial target := by
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (rows_mem p cs bound c hc q hq))

theorem rows_consistent {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) {before after : SemanticTranscript Hash}
    {cs : List (SourceFull25.Call D pre)} (run : SourceFull25.Trace D pre before after cs)
    (bound : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32) :
    let H := SourceDigestOracle.oracle D before.hash pubInput root length
    ∀ q ∈ rows p cs bound, q.2 = H q.1 := by
  dsimp only
  intro q hq
  obtain ⟨c,hc,hq⟩ := List.mem_flatMap.mp hq
  have hf := SourceDigestOracle.trace_functional p run pubInput root length bound c.val c.property
  simp only [row, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2

/-- Initial/target equations are explicit boundaries only in this generic
helper. The actual caller supplies both via its real digest successes. -/
theorem relevant_consistent {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) {before after : SemanticTranscript Hash}
    {cs : List (SourceFull25.Call D pre)} (run : SourceFull25.Trace D pre before after cs)
    (bound : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (initial target : Observation L)
    (hi : initial.2 = SourceDigestOracle.oracle D before.hash pubInput root length initial.1)
    (ht : target.2 = SourceDigestOracle.oracle D before.hash pubInput root length target.1) :
    ∀ q ∈ relevant p cs bound initial target,
      q.2 = SourceDigestOracle.oracle D before.hash pubInput root length q.1 := by
  intro q hq
  simp only [relevant, List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | hr | rfl
  · exact hi
  · exact rows_consistent p run bound pubInput root length q hr
  · exact ht

theorem read_of_mem {L : Nat} (tr : List (Observation L)) (q : Observation L)
    (hq : q ∈ tr) : Read tr q.1 := List.mem_map.mpr ⟨q,hq,rfl⟩

theorem read_initial {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D)
    (initial target : Observation L) : Read (relevant p cs bound initial target) initial.1 :=
  read_of_mem _ initial (by simp [relevant])

theorem read_target {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D)
    (initial target : Observation L) : Read (relevant p cs bound initial target) target.1 :=
  read_of_mem _ target (by simp [relevant])

theorem read_row {Hash M Cv : Type} {L : Nat} {D : aspis_core.Digest32 Hash} {pre : Prefix}
    (p : Params M Cv L) (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (rawBytes c.record.framed).length ≤ p.D)
    (initial target : Observation L)
    (c : SourceFull25.Call D pre) (hc : c ∈ cs) (q : Observation L)
    (hq : q ∈ row p c (bound c hc)) : Read (relevant p cs bound initial target) q.1 :=
  read_of_mem _ q (relevant_row_mem p cs bound initial target c hc q hq)

/-- Optional inclusion of the source-observation subtrace in a supplied whole
trace. No exact count/order of the external runtime log is asserted. -/
theorem read_in_whole {L : Nat} (sub whole : List (Observation L))
    (included : ∀ q ∈ sub, q ∈ whole) (address : Addr L) (hr : Read sub address) :
    Read whole address := by
  obtain ⟨q,hq,he⟩ := List.mem_map.mp hr
  exact List.mem_map.mpr ⟨q,included q hq,he⟩

#print axioms row
#print axioms rows
#print axioms relevant
#print axioms row_length
#print axioms rows_length
#print axioms relevant_length
#print axioms rows_mem
#print axioms relevant_row_mem
#print axioms rows_consistent
#print axioms relevant_consistent
#print axioms read_of_mem
#print axioms read_initial
#print axioms read_target
#print axioms read_row
#print axioms read_in_whole
end AspisR1PublicPreparation.SourceObservations
end
