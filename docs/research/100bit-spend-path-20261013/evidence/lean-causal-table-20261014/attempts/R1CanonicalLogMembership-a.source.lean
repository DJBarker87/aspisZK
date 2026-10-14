import R1CanonicalOracleLog

/-! Membership characterization and extensionality for the canonical byte
log extracted from an address/state trace. -/
set_option autoImplicit false
namespace AspisR1.CanonicalLogMembership

open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CanonicalByteAddress MerkleRecordedLog

variable {L : Nat}

theorem mem_byteLog {tr : List (Addr L × State)} {input : List Merkle32Path.Byte}
    {output : Merkle32Path.Digest} :
    (input, output) ∈ CanonicalOracleLog.byteLog tr ↔
      ∃ a, (a, output) ∈ tr ∧ Canonical a ∧ a.toBytes = input := by
  change (input, output) ∈
      (CanonicalOracleLog.canonicalTrace tr).map (fun q => (q.1.toBytes, q.2)) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨a, answer⟩, hq, hpair⟩
    have hpair' : a.toBytes = input ∧ answer = output := by
      simpa only [Prod.mk.injEq] using hpair
    refine ⟨a, ?_, (CanonicalOracleLog.mem_canonicalTrace.mp hq).2, hpair'.1⟩
    exact List.mem_map.mpr ⟨(a, answer),
      (CanonicalOracleLog.mem_canonicalTrace.mp hq).1, by simp [hpair'.2]⟩
  · rintro ⟨a, ha, hcanonical, hbytes⟩
    refine ⟨(a, output), ?_, ?_⟩
    · exact CanonicalOracleLog.mem_canonicalTrace.mpr ⟨ha, hcanonical⟩
    · simp [hbytes]

theorem byteLog_mem_eq (tr1 tr2 : List (Addr L × State))
    (hraw : ∀ a output, (a, output) ∈ tr1 ↔ (a, output) ∈ tr2) :
    ∀ input output,
      (input, output) ∈ CanonicalOracleLog.byteLog tr1 ↔
        (input, output) ∈ CanonicalOracleLog.byteLog tr2 := by
  intro input output
  rw [mem_byteLog, mem_byteLog]
  constructor
  · rintro ⟨a, ha, hc, hbytes⟩
    exact ⟨a, (hraw a output).mp ha, hc, hbytes⟩
  · rintro ⟨a, ha, hc, hbytes⟩
    exact ⟨a, (hraw a output).mpr ha, hc, hbytes⟩

#print axioms mem_byteLog
#print axioms byteLog_mem_eq

end AspisR1.CanonicalLogMembership
