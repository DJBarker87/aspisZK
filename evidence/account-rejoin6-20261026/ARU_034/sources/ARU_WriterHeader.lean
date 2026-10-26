import ARU_Header
import SCH_Oracle
import GExp_FirstErasure
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_WriterHeader
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge

/-- The total dictionary here is a mathematical interpreter, not a native
syscall assumption. Only the successful issued writer is consumed. -/
theorem ideal (H : Bytes → State) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (success : (eval H (SdkC_Oracle.program (GExp_FirstCode.writerCode p a proof pub))).2 = ok saved) :
    CPhy_Header.decode (MultiproofConeCanonical.bytesOf saved.val) =
      some (H (MultiproofConeCanonical.bytesOf proof.val),H (MultiproofConeCanonical.bytesOf pub.val)) ∧
    saved.val.length = 1768 := by
  let D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit :=
    ⟨⟨⟨fun u => ok u⟩⟩,fun _ parts => SCH_Oracle.ideal H parts⟩
  have source := (SCH_Oracle.evaluation H (GExp_FirstCode.writerCode p a proof pub) []).1.trans success
  rw [SdkC_Source.erasure,GExp_FirstErasure.writer (SCH_Oracle.ideal H) D (fun _ => rfl)] at source
  apply ARU_Header.writer (Tx1Q_Install.digest D) () H (Tx1Q_Carriers.prepared p)
    (Tx1Q_Carriers.accumulator a) proof pub saved _ source
  intro parts digest issued returned
  have same : encodeState (H (flatten parts)) = digest := Result.ok.inj returned
  rw [←same]
  exact state_roundtrip _

#print axioms ideal
end AspisR1.ARU_WriterHeader
end
