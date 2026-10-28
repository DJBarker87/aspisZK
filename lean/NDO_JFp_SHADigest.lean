import NDO_JFp_InitBytes
import NDO_JFr_SeedBoundary
set_option autoImplicit false
namespace AspisR1.JFp_SHADigest
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation

def registers (s : JFp_SHA256.Reg) : List Nat := [s.a,s.b,s.c,s.d,s.e,s.f,s.g,s.h]
def output (s : JFp_SHA256.Reg) : State := fun i =>
  ⟨((registers s).getD (i.val/4) 0 / 256^(3-i.val%4)) % 256, Nat.mod_lt _ (by decide)⟩
def digest (b : Bytes) : State := output (JFp_SHA256.hash (b.map Fin.val))

theorem seed : digest (flatten (TranscriptStep.initParts
    (alloc.vec.Vec.deref JFs_ExactSerialization.encoded) JFp_InitBytes.root 1455#u32))=
      JFr_SeedBoundary.numeric := by
  unfold digest
  rw [JFp_InitBytes.native,JFp_InitBytes.regroup,JFp_SeedHash.checked]
  funext i
  fin_cases i <;> rfl

/-- Concrete mathematical SHA256 is installed as H; no arbitrary-oracle seed equation. -/
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    r1_semantic.public_transcript
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current digest D))
      JFs_PublicSerialization.value hash JFp_InitBytes.root=ok (.Ok
        (⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  have h := JFs_ExactInitialization.source digest D hash JFp_InitBytes.root
  simpa only [MultiproofConePhysicalTransport.rawOracle,seed] using h

#print axioms seed
#print axioms source
end AspisR1.JFp_SHADigest
