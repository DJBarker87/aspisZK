import RPz7_F3W_SourceLog
import RPz7_F3W_FirstLog
import RPz7_F3V_EvidenceCalls
import RPz7_F3U_RehashValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_Preparation
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

def code {F C : Type} (c : Configuration F C) (semantic : Port1_Driver.Semantic)
    (proof : Slice U8) (zero : AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact) :=
  SdkD_PrepareLower.lower (SdkD_PrepareSource.code
    (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std
    (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic) proof () (Array.repeat 29#usize zero))

def program {F C : Type} (c : Configuration F C) (s : Submission) :
    Program Bytes State (Option AspisR1CurrentCaller.verifier.Prepared) :=
  match Port1_Driver.asSlice s.publicBytes,Port1_Driver.asSlice s.stored with
  | some pub,some proof =>
    match Port1_Driver.decodeSemantic (sdk c) pub with
    | .ok (some semantic) =>
      match AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO
        (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std) with
      | .ok zero => bind (SdkC_Oracle.program (code c semantic proof zero)) fun r =>
        .done (match r with | .ok (.Ok p,_) => some p | _ => none)
      | _ => .done none
    | _ => .done none
  | _,_ => .done none

theorem on_evidence {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission) (H : Bytes → State)
    (e : Evidence c B s H) :
    eval H (program c s)=
      (AuS1_Recovery.log (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
        e.proof () (Array.repeat 29#usize e.run.zero),some e.run.p) := by
  have pub : Port1_Driver.asSlice s.publicBytes=some e.pub := by
    rw [←e.pubBytes];exact F3U_Slice.roundtrip _
  have proof : Port1_Driver.asSlice s.stored=some e.proof := by
    rw [←e.proofBytes];exact F3U_Slice.roundtrip _
  simp only [program,pub,proof,e.decoded,e.zero,eval_bind]
  have same := F3V_LoweredPreparation.same H (currentDigest c)
    (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std
    (AspisS6CurrentVerifierCarrier.toPublic e.semantic) e.proof () (Array.repeat 29#usize e.run.zero)
  have result : (eval H (SdkC_Oracle.program (code c e.semantic e.proof e.run.zero))).2=
      ok (.Ok e.run.p,e.run.scratch) := by
    rw [code,same,SdkD_PrepareLower.program,F3U_RehashValue.value]
    rw [F3V_SdkPreparation.same]
    rw [SdkD_PrepareSource.source]
    change AspisR1CurrentCaller.verifier.candidate.prepare _ (D1 c H) _ _ _ _ _=_
    exact F3V_EvidenceCalls.preparation c B s H e
  have logs := AuS1_Observe.lower (F3U_Oracle.hashv H)
    (SdkD_PrepareSource.code (Uni_Install.current c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std (D1 c H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
      e.proof () (Array.repeat 29#usize e.run.zero))
    (AuS1_Prepare.uniform _ _ _ _ (F3U_Oracle.hashv H) (fun _ _=>rfl) _ _ _ _) []
  have trace := congrArg Prod.fst (F3U_ReifyExact.exact (code c e.semantic e.proof e.run.zero) H)
  rw [code,same] at trace
  rw [show SdkC_Source.readLog []=[] from rfl,List.nil_append] at logs
  change _=AuS1_Recovery.log _ _ _ _ _ _ _ _ at logs
  rw [result,eval,List.append_nil]
  apply Prod.ext
  · change (eval H (SdkC_Oracle.program (code c e.semantic e.proof e.run.zero))).1=_
    rw [code,same]
    exact trace.trans logs
  · rfl

#print axioms on_evidence
end AspisR1.F3X_Preparation
end
