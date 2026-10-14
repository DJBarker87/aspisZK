import R1CanonicalOracleLog

/-! Recover the canonical address behind an encoded input found in the
canonical byte log. These are list/address plumbing lemmas only. -/
set_option autoImplicit false
namespace AspisR1.CanonicalLogInputs

open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.CanonicalByteAddress AspisR1.CanonicalByteHash

variable {L : Nat}

theorem mem_input {tr : List (Addr L × State)} {input : Bytes}
    (hin : input ∈ (CanonicalOracleLog.byteLog tr).map Prod.fst) :
    ∃ a, Read tr a ∧ Canonical a ∧ a.toBytes = input := by
  change input ∈
    ((CanonicalOracleLog.canonicalTrace tr).map
      (fun q => (q.1.toBytes, q.2))).map Prod.fst at hin
  obtain ⟨entry, hentry, hfst⟩ := List.mem_map.mp hin
  obtain ⟨q, hq, hpair⟩ := List.mem_map.mp hentry
  have hcanonical := CanonicalOracleLog.mem_canonicalTrace.mp hq
  have hbytes : q.1.toBytes = input := by
    exact (congrArg Prod.fst hpair).trans hfst
  refine ⟨q.1, ?_, hcanonical.2, hbytes⟩
  exact List.mem_map.mpr ⟨q, hcanonical.1, rfl⟩

theorem input_length_le {tr : List (Addr L × State)} {input : Bytes}
    (hin : input ∈ (CanonicalOracleLog.byteLog tr).map Prod.fst) :
    input.length ≤ L := by
  obtain ⟨a, _, _, hbytes⟩ := mem_input hin
  rw [← hbytes]
  exact CanonicalByteAddress.length_le a

theorem input_read {tr : List (Addr L × State)} {input : Bytes}
    (hin : input ∈ (CanonicalOracleLog.byteLog tr).map Prod.fst) :
    Read tr (CanonicalByteHash.encode input) := by
  obtain ⟨a, hread, hcanonical, hbytes⟩ := mem_input hin
  rw [← hbytes, CanonicalByteHash.encode_toBytes, hcanonical]
  exact hread

theorem encode_ne {left right : Bytes} (hlenLeft : left.length ≤ L)
    (hlenRight : right.length ≤ L) (hne : left ≠ right) :
    (CanonicalByteHash.encode left : Addr L) ≠ CanonicalByteHash.encode right := by
  intro heq
  apply hne
  have hbytes := congrArg Addr.toBytes heq
  rw [CanonicalByteHash.toBytes_encode left hlenLeft,
    CanonicalByteHash.toBytes_encode right hlenRight] at hbytes
  exact hbytes

#print axioms mem_input
#print axioms input_length_le
#print axioms input_read
#print axioms encode_ne

end AspisR1.CanonicalLogInputs
