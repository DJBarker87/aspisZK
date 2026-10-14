import R1CanonicalByteHash
import R1MerkleRecordedTargets
import R1MerkleLogRecovery

/-! Extract byte records only from canonical bounded-address queries. This
keeps arbitrary noncanonical prover queries in the full trace/budget, but
does not confuse their independent oracle cells with byte-string queries. -/
set_option autoImplicit false
namespace AspisR1.CanonicalOracleLog

open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CanonicalByteAddress CanonicalByteHash
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog

variable {L : Nat}

instance canonicalDecidable (a : Addr L) : Decidable (Canonical a) :=
  inferInstanceAs (Decidable (normalize a = a))

def canonicalTrace (tr : List (Addr L × State)) : List (Addr L × State) :=
  tr.filter fun q => decide (Canonical q.1)

theorem mem_canonicalTrace {tr : List (Addr L × State)} {q : Addr L × State} :
    q ∈ canonicalTrace tr ↔ q ∈ tr ∧ Canonical q.1 := by
  simp [canonicalTrace]

def byteLog (tr : List (Addr L × State)) : Log :=
  MerkleRecordedTargets.byteLog (canonicalTrace tr)

theorem read_original {tr : List (Addr L × State)} {a : Addr L}
    (h : Read (canonicalTrace tr) a) : Read tr a := by
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨q, (mem_canonicalTrace.mp hq).1, heq⟩

theorem consistent (H : Addr L → State) (tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) :
    MerkleRecordedLog.Consistent (hashBytes H) (byteLog tr) := by
  intro input output hentry
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hentry
  cases heq
  have hc := mem_canonicalTrace.mp hq
  change hashBytes H q.1.toBytes = q.2
  rw [hashBytes_toBytes_canonical H q.1 hc.2]
  exact (hcons q hc.1).symm

theorem encoded_present (tr : List (Addr L × State)) (input : Bytes)
    (hlen : input.length ≤ L) (hread : Read tr (encode input)) :
    input ∈ (byteLog tr).map Prod.fst := by
  obtain ⟨⟨a, output⟩, hentry, heq⟩ := List.mem_map.mp hread
  dsimp at heq
  subst a
  apply List.mem_map.mpr
  refine ⟨(input, output), ?_, rfl⟩
  apply List.mem_map.mpr
  refine ⟨(encode input, output), ?_, ?_⟩
  · exact mem_canonicalTrace.mpr ⟨hentry, encode_canonical input⟩
  · simp only [toBytes_encode input hlen]

theorem absent_encoded_not_read (tr : List (Addr L × State)) (input : Bytes)
    (hlen : input.length ≤ L) (habsent : input ∉ (byteLog tr).map Prod.fst) :
    ¬ Read tr (encode input) := by
  intro hread
  exact habsent (encoded_present tr input hlen hread)

theorem target_cases (tr : List (Addr L × State)) (root target : State)
    (h : target ∈ targets (nodes (byteLog tr)) root) :
    target = root ∨ ∃ b, Read tr b ∧ ∃ j : Fin 8,
      MerkleChildTargets.pred j b = some target := by
  rcases MerkleRecordedTargets.target_cases (canonicalTrace tr) root target h with
    heq | ⟨b, hb, j, hp⟩
  · exact Or.inl heq
  · exact Or.inr ⟨b, read_original hb, j, hp⟩

theorem recover_or_bad (H : Addr L → State) (pre : List (Addr L × State))
    (hcons : ∀ q ∈ pre, q.2 = H q.1) (tag : Merkle32Path.Byte) (width : Nat)
    (packed salt : List Merkle32Path.Byte) (hw : packed.length = width)
    (hs : salt.length = 32) {slots : List (Fin 8)} (path : Path slots) (root : State)
    (hroot : root = foldPath (hashBytes H) path
      (hashBytes H (leafInput tag packed salt))) :
    recover (nodes (byteLog pre)) (leaves tag width (byteLog pre)) slots root =
        some (packed, salt) ∨
      CrossTraceCollision (hashBytes H) ((byteLog pre).map Prod.fst)
        (fullTrace (hashBytes H) path (leafInput tag packed salt)) ∨
      MerkleLogRecovery.AbsentTargetHit (hashBytes H) (byteLog pre) root
        (fullTrace (hashBytes H) path (leafInput tag packed salt)) := by
  exact MerkleLogRecovery.recover_or_bad (hashBytes H) (byteLog pre)
    (consistent H pre hcons) tag width packed salt hw hs path root hroot

#print axioms canonicalDecidable
#print axioms mem_canonicalTrace
#print axioms read_original
#print axioms consistent
#print axioms encoded_present
#print axioms absent_encoded_not_read
#print axioms target_cases
#print axioms recover_or_bad

end AspisR1.CanonicalOracleLog
