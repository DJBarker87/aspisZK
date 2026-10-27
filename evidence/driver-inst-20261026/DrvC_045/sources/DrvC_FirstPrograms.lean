import DrvC_QueryTransport
import DrvC_FirstBatch
import DrvC_FirstPrepare
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstPrograms
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers DrvC_OraclePort
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem shape {F C : Type} (c : Configuration F C) (proof : Slice U8) :
    SdkC_Oracle.program (DrvC_CallCode.code c (.op3 proof)) =
      mapR (DrvC_Dictionary.reply variant) (.done ((currentInstalled c).op3 proof)) := by
  rw [DrvC_CallCode.implementation]
  rw [map_lift,DrvC_FirstPure.shape]
  rfl

theorem scan {F C : Type} (c : Configuration F C) (proof : Slice U8) :
    SdkC_Oracle.program (DrvC_CallCode.code c (.op4 proof)) =
      mapR (DrvC_Dictionary.reply id) (.done ((currentInstalled c).op4 proof)) := by
  rw [DrvC_CallCode.implementation]
  rfl

theorem zero {F C : Type} (c : Configuration F C) :
    SdkC_Oracle.program (DrvC_CallCode.code c .op1) =
      mapR e (.done (AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO (currentInstalled c))) := by
  rw [DrvC_CallCode.implementation]
  rfl

theorem initial {F C : Type} (c : Configuration F C) :
    SdkC_Oracle.program (DrvC_CallCode.code c (.op12 .S2)) =
      mapR (DrvC_Dictionary.reply accumulator) (.done ((currentInstalled c).op20 .S2)) := by
  rw [DrvC_CallCode.implementation]
  rfl

theorem query {F C : Type} (c : Configuration F C) (proof : Slice U8)
    (p : Tx1Q_Carriers.C.P) (a : Tx1Q_Carriers.C.A) (g : Array Tx1Q_Carriers.C.E 29#usize)
    (geo : Tx1Q_Carriers.C.G) (b : Tx1Q_Carriers.C.B) (stop : Usize) :
    SdkC_Oracle.program (DrvC_CallCode.code c
      (.op6 proof (prepared p) (accumulator a) (arr e g) none (geometry geo) (pending b) stop)) =
    mapR (DrvC_Dictionary.reply (fun out => (accumulator out.1,pending out.2)))
      (.done ((currentInstalled c).op7 proof p a g none geo b stop)) := by
  rw [DrvC_CallCode.implementation]
  rw [map_lift,DrvC_QueryTransport.query]
  rfl

theorem pending_call {F C : Type} (c : Configuration F C) (weights : Slice Tx1Q_Carriers.C.K) :
    SdkC_Oracle.program (DrvC_CallCode.code c (.op10 (slice k weights))) =
      mapR (DrvC_Dictionary.reply pending) (.done ((currentInstalled c).op18 weights)) := by
  rw [DrvC_CallCode.implementation]
  rw [map_lift,DrvC_QueryTransport.pending_call]
  rfl

theorem geometry_call {F C : Type} (c : Configuration F C) (qs : Array U32 22#usize) (start stop : Usize) :
    SdkC_Oracle.program (DrvC_CallCode.code c (.op11 qs start stop)) =
      mapR (DrvC_Dictionary.reply geometry) (.done ((currentInstalled c).op19 qs start stop)) := by
  rw [DrvC_CallCode.implementation]
  rw [map_lift,DrvC_QueryTransport.geometry_call]
  rfl

theorem flush {F C : Type} (c : Configuration F C) (b : Tx1Q_Carriers.C.B) (old : Slice Tx1Q_Carriers.C.K) :
    SdkC_Oracle.program (DrvC_CallCode.code c (.op9 (pending b) (slice k old))) =
      mapR (slice k) (.done ((currentInstalled c).op17 b old)) := by
  rw [DrvC_CallCode.implementation]
  rw [map_lift,DrvC_FirstPure.flush]
  rfl

theorem prepare {F C : Type} (c : Configuration F C) (semantic : Port1_Driver.Semantic)
    (proof : Slice U8) (g : Array Tx1Q_Carriers.C.E 29#usize) :
    SdkC_Oracle.program (DrvC_CallCode.code c (.op7 (digest c) semantic proof () none (arr e g))) =
      mapR DrvC_Dictionary.prepareReply
        (SdkC_Oracle.program (SdkD_PrepareLower.lower (SdkD_PrepareSource.code
          (Op5T_Concrete.current
            {GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry with op16 := Tx1Q_Install.writer})
          c.boundaries c.std (currentDigest c)
          (AspisS6CurrentVerifierCarrier.toPublic semantic) proof () g))) := by
  rw [DrvC_FirstPrepare.code,DrvC_Program.program_map]
  rfl

theorem batch {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (proof : Slice U8) (p : Tx1Q_Carriers.C.P) (root : Array U8 32#usize) :
    SdkC_Oracle.program (DrvC_CallCode.code c (.op5 (digest c) proof (prepared p) root 0#usize ())) =
      mapR (DrvC_Dictionary.reply id) (SdkC_Oracle.program (SdkC_BatchSource.currentCode hashv proof p root)) := by
  rw [DrvC_FirstBatch.batch c hashv,DrvC_Program.program_map]
  rfl

#print axioms shape
#print axioms scan
#print axioms zero
#print axioms initial
#print axioms query
#print axioms pending_call
#print axioms geometry_call
#print axioms flush
#print axioms prepare
#print axioms batch
end AspisR1.DrvC_FirstPrograms
end
