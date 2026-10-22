import CheckpointBytes5Trace
import CheckpointBytes4SuccessfulFields
import WireTx2Records
import RawDigestLogCarrier

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes5Inputs
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical CheckpointBytesDigest
open AspisR1DigestLogCarrier (flatten)
open AspisR1Stage2.WireTx2 (singletonParts checksumParts checksumDomain)

def observe (log : Log) : List (Bytes × State) :=
  log.map (fun event => (flatten event.1,stateOf event.2))

/-- The fixed ROM/carrier interpretation, stated per call, never per trace. -/
def Oracle {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) : Prop :=
  ∀ parts digest, D.digest hash parts = ok digest → stateOf digest = H (flatten parts)

theorem singleton_input (s : Slice U8) : flatten (singletonParts s) = bytesOf s.val := by
  change bytesOf (s.val ++ []) = bytesOf s.val
  rw [List.append_nil]

theorem checksum_input (s : Slice U8) :
    flatten (checksumParts s) = OraclePortPhysicalFrameDraft.domain ++ bytesOf s.val := by
  change bytesOf (checksumDomain.val ++ (s.val ++ [])) = _
  simp only [List.append_nil,bytesOf,List.map_append]
  rfl

theorem calls_inputs {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (ck proof public1 : Slice U8) (c : Tx2ResumeDigests.Calls D hash ck proof public1)
    (length : ck.val.length = 1768) :
    flatten c.proofParts = bytesOf proof.val ∧
    flatten c.publicParts = bytesOf public1.val ∧
    flatten c.checksumParts =
      OraclePortPhysicalFrameDraft.domain ++ (bytesOf ck.val).take 1736 := by
  have pp : c.proofParts = singletonParts proof := by
    simpa only [lift,singletonParts,Result.ok.injEq] using c.proofInput.symm
  have pu : c.publicParts = singletonParts public1 := by
    simpa only [lift,singletonParts,Result.ok.injEq] using c.publicInput.symm
  have dom : c.checksumDomain = checksumDomain := by
    simpa only [lift,checksumDomain,Result.ok.injEq] using c.domainInput.symm
  have cp : c.checksumParts = checksumParts c.checksumBody := by
    simpa only [lift,checksumParts,dom,Result.ok.injEq] using c.checksumInput.symm
  have endValue : c.checksumEnd.val = 1736 := by
    have h := UScalar.sub_equiv (Slice.len ck) 32#usize
    rw [c.end_eq] at h
    dsimp only at h
    have hv := h.2.1
    change ck.val.length = c.checksumEnd.val+32 at hv
    omega
  have body : c.checksumBody.val = ck.val.take 1736 := by
    have h := c.bodyInput
    simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice,
      core.slice.index.SliceIndexRangeToUsizeSlice.index] at h
    split at h
    · have eq := congrArg Subtype.val (Result.ok.inj h)
      simpa only [List.slice,List.drop_zero,endValue] using eq.symm
    · cases h
  refine ⟨pp ▸ singleton_input proof, pu ▸ singleton_input public1,?_⟩
  rw [cp,checksum_input,body]
  simp only [bytesOf,List.map_take]

theorem calls_observation {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (H : Bytes → State) (oracle : Oracle D hash H)
    (ck proof public1 : Slice U8) (c : Tx2ResumeDigests.Calls D hash ck proof public1)
    (length : ck.val.length = 1768) :
    let stored := bytesOf proof.val
    let pub := bytesOf public1.val
    let address := OraclePortPhysicalFrameDraft.domain ++ (bytesOf ck.val).take 1736
    observe [(c.proofParts,c.proofDigest),(c.publicParts,c.publicDigest),
      (c.checksumParts,c.checksumDigest)] =
        [(stored,H stored),(pub,H pub),(address,H address)] := by
  obtain ⟨pp,pu,pc⟩ := calls_inputs D hash ck proof public1 c length
  simp only [observe,List.map_cons,List.map_nil,
    oracle _ _ c.proofCall,oracle _ _ c.publicCall,oracle _ _ c.checksumCall,pp,pu,pc]

#print axioms singleton_input
#print axioms checksum_input
#print axioms calls_inputs
#print axioms calls_observation
end AspisR1.CheckpointBytes5Inputs
end
