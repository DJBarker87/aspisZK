import S2Z_Oracle

set_option autoImplicit false
noncomputable section
namespace AspisR1.S2Z.Oracle
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- The total Required14 field needs only the successful-call runtime law
plus a separately proved returning domain, not an assumed encoded digest law.
The representation roundtrip is already proved in the existing bridge. -/
theorem total_of_returning (ops : AdapterRw.Ops) (hashv : Parts → Result Digest)
    (sha256 H : Bytes → State) (binding : NativeBinding ops hashv)
    (runtime : RuntimeSyscall hashv sha256) (p1 : P1Realization sha256 H)
    (returns : ∀ parts, ∃ digest, hashv parts = ok digest) :
    ∀ parts, (leadDigest ops).digest () parts =
      ok (MultiproofConePhysicalTransport.rawOracle H parts) := by
  intro parts
  obtain ⟨digest,returned⟩ := returns parts
  have call : (leadDigest ops).digest () parts = ok digest := by
    change ops.op43 () parts = ok digest
    rw [binding]
    exact returned
  have value := successful_call ops hashv sha256 H binding runtime p1 parts digest call
  change AspisV8R19.SqueezeOracleBridge.decodeState digest =
    H (AspisV8R19.SqueezeOracleBridge.flatten parts) at value
  have raw : digest = MultiproofConePhysicalTransport.rawOracle H parts := by
    change digest = AspisV8R19.SqueezeOracleBridge.encodeState
      (H (AspisV8R19.SqueezeOracleBridge.flatten parts))
    rw [← value]
    exact (AspisV8R19.SqueezeOracleBridge.array_roundtrip digest).symm
  exact call.trans (congrArg Result.ok raw)

#print axioms total_of_returning
end AspisR1.S2Z.Oracle
end
