import R9PoolRuntimeBinding

/-! Logical list facts for the source-pinned raw framing cuts. The Kani
receipts separately check the Rust slice identities. No whole-driver join. -/
set_option autoImplicit false
namespace AspisR1.StoredCarrierRawLayout
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open R9PoolRuntimeBinding

abbrev candidateBytes : Nat := 688
abbrev proofBytes : Nat := 57607
abbrev rawBytes : Nat := candidateBytes + proofBytes
abbrev checkpointBytes : Nat := 1768
abbrev publicBytes : Nat := 1880

def rawProof (account : Bytes) : Bytes :=
  (account.drop candidateBytes).take proofBytes

/-- Raw admission has no legacy 40-byte header and no 1768-byte tail. -/
theorem raw_length (candidate proof : Bytes)
    (hc : candidate.length = candidateBytes) (hp : proof.length = proofBytes) :
    (candidate ++ proof).length = 58295 := by
  rw [List.length_append, hc, hp]
  rfl

/-- Both admitted readers select the complete proof after the candidate. -/
theorem raw_read (candidate proof : Bytes)
    (hc : candidate.length = candidateBytes) (hp : proof.length = proofBytes) :
    rawProof (candidate ++ proof) = proof := by
  unfold rawProof
  rw [← hc, List.drop_left]
  exact List.take_of_length_le (by omega)

/-- Legacy ASPU framing is not an alternative admitted layout: even its
smallest proof account has 40 header bytes plus a separate 1768-byte tail. -/
theorem legacy_length_rejected (header candidate proof tail : Bytes)
    (hh : header.length = 40) (hc : candidate.length = candidateBytes)
    (hp : proof.length = proofBytes) (ht : tail.length = checkpointBytes) :
    (header ++ candidate ++ proof ++ tail).length ≠ rawBytes := by
  simp only [List.length_append, hh, hc, hp, ht]
  decide

/-- This is P2′ at exactly the two full-buffer digest checks, reused rather
than inferred from hash equality. It implies equality for every byte reader. -/
theorem same_readers (hash : Bytes → State) (written current : Inputs)
    (hP2 : P2Prime hash written current) (matched : digestMatches hash written current) :
    current = written ∧ rawProof current.proof = rawProof written.proof := by
  have h := accepted_same_inputs hash written current hP2 matched
  exact ⟨h, congrArg (fun i : Inputs => rawProof i.proof) h⟩

/-- Upload history need not be honest: only the final bytes consumed matter.
Equal complete accounts give equal slices even after arbitrary staging. -/
theorem staging_extensional (history : List Bytes) (written current : Bytes)
    (last_upload : history.getLast? = some written) (persisted : current = written) :
    rawProof current = rawProof written ∧ history.getLast? = some current := by
  subst current
  exact ⟨rfl, last_upload⟩

#print axioms raw_length
#print axioms raw_read
#print axioms legacy_length_rejected
#print axioms same_readers
#print axioms staging_extensional
end AspisR1.StoredCarrierRawLayout
