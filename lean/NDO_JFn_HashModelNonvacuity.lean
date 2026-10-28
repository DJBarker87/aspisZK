import NDO_JFn_HashLengths
import NDO_JFn_Resume
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_HashModelNonvacuity
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-- A finite model-oracle extension, NOT an implementation or a claimed
realization of SHA256. Its purpose is checking consistency of the three
remaining premises. All other query inputs retain the supplied background. -/
def extension (background : Bytes → State) (input : Bytes) : State :=
  if input=flatten JFn_HashBoundary.proofParts then decodeState JFo_AuthBytes.proofHash
  else if input=flatten JFn_HashBoundary.publicParts then decodeState JFo_AuthBytes.publicHash
  else if input=flatten JFn_HashBoundary.checksumParts then decodeState JFo_AuthBytes.checksum
  else background input

theorem realizes (background : Bytes → State) : JFn_HashBoundary.Realizes (extension background) := by
  obtain ⟨hp, hc, hu⟩ := JFn_HashLengths.distinct
  unfold JFn_HashBoundary.Realizes extension
  simp only [hp,hp.symm,hc,hc.symm,hu,hu.symm,ite_false,ite_true,true_and]

theorem unchanged (background : Bytes → State) (input : Bytes)
    (hp : input≠flatten JFn_HashBoundary.proofParts)
    (hu : input≠flatten JFn_HashBoundary.publicParts)
    (hc : input≠flatten JFn_HashBoundary.checksumParts) : extension background input=background input := by
  simp only [extension,hp,hu,hc,ite_false]

/-- Model-only reader non-vacuity at the retained physical bytes. This is
not the real SHA256 native wrapper, and it closes no deployed-top premise. -/
theorem reader {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (background : Bytes → State) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary (extension background) D)
      JFx_NativeBytes.checkpoint JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) :=
  JFn_Resume.source _ D hash (realizes background)

#print axioms realizes
#print axioms unchanged
#print axioms reader
end AspisR1.JFn_HashModelNonvacuity
end
