import CPH_Install
import SAQ_CompleteInstall
import SAP_Binding
import F3U_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFx_SourcePorts
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def select {F C : Type} (c : DrvC_Installation.Configuration F C)
    (indexError : C) (H : Bytes → State) : DrvC_Installation.Configuration F C :=
  {SAQ_CompleteInstall.select indexError c with
    adapter := {c.adapter with op43 := S2W_DigestExtraction.digest (F3U_Oracle.hashv H)}
    boundaries := F3M_CircleSource.install c.boundaries}

def configuration {F C : Type} (c : DrvC_Installation.Configuration F C)
    (indexError : C) (H : Bytes → State) :=
  CPH_Install.configuration (select c indexError H) (.Ok ())

def first {F C : Type} (c : DrvC_Installation.Configuration F C)
    (indexError : C) (H : Bytes → State) : S2W_ExtractionBoundary.First :=
  AdapterRw.r1_pool_adapter.owned.stage1_owned (DrvC_Installation.sdk (configuration c indexError H))

def second {F C : Type} (c : DrvC_Installation.Configuration F C)
    (indexError : C) (H : Bytes → State) : S2W_ExtractionBoundary.Second :=
  AdapterRw.r1_pool_adapter.owned.stage2_owned (DrvC_Installation.sdk (configuration c indexError H))

/-- Universal owner ports and extraction coexist on ONE selected dictionary
with actual extracted natives. Neither native acceptance nor the raw frozen3
join is asserted. These are source instances, not new trust assumptions. -/
theorem jointly {F C : Type} (c : DrvC_Installation.Configuration F C)
    (indexError : C) (H : Bytes → State) :
    let r := configuration c indexError H
    S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk r)
      (first c indexError H) (second c indexError H) (F3U_Oracle.hashv H) ∧
    WAdm_Domain.SessionAPrepare (Tx1Q_Execution.actual (Op5T_Concrete.current r.currentBase)
      r.reserved r.query r.geometry r.boundaries r.std) ∧
    Port5Q1_QueryPorts.SessionAPrimitives r.query ∧
    Port5Q1_GeometryCanonical.SessionAPrimitives r.geometry ∧
    Port5Q1_Domain.SessionADomain r.geometry ∧
    r.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul ∧
    r.geometry.op7=ok 1#u32 ∧
    r.geometry.op11=Port4C_InverseExecution.inverse_owned ∧
    S2W_ExtractionBoundary.P1 H H ∧
    S2W_ExtractionBoundary.RuntimeSyscall (F3U_Oracle.hashv H) H := by
  refine ⟨⟨by intros; rfl,by intros; rfl,by intros; rfl⟩,?_,
    SAQ_Decoder.primitives c.query,SAQ_Constructor.canonical indexError c.geometry,
    SAQ_Constructor.domain indexError c.geometry,rfl,rfl,
    SAQ_Constructor.inverse indexError c.geometry,⟨fun _ => rfl⟩,F3U_Oracle.syscall H⟩
  exact SAP_Binding.prepare
    (CPP_Install.configuration (Rc2_Install.select (select c indexError H) (.Ok ())))

#print axioms jointly
end AspisR1.JFx_SourcePorts
end
