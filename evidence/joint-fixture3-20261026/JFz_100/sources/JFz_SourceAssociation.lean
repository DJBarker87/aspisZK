import Rc5_Install
import F3U_Oracle
import JFz_Parsed
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_SourceAssociation
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Only the digest leaf is selected here. Every other Rc5 body is the adopted
installed body. This remains parameterized by a seed, not an accepted fixture. -/
def seed {F C : Type} (c : DrvC_Installation.Configuration F C) (H : Bytes → State) :=
  {c with adapter := {c.adapter with op43 := S2W_DigestExtraction.digest (F3U_Oracle.hashv H)}}

def configuration {F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (r : NP6_StdModel.Reservation) (H : Bytes → State) :=
  Rc5_Install.configuration err (seed c H) r

def first {F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (r : NP6_StdModel.Reservation) (H : Bytes → State) :=
  AdapterRw.r1_pool_adapter.owned.stage1_owned (DrvC_Installation.sdk (configuration c err r H))

def second {F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (r : NP6_StdModel.Reservation) (H : Bytes → State) :=
  AdapterRw.r1_pool_adapter.owned.stage2_owned (DrvC_Installation.sdk (configuration c err r H))

/-- Rc5 extraction and model syscall share one actual source dictionary. This
asserts no success of either source function. Its real-byte parser preflight
is included explicitly; acceptance of the enclosing source is still open. -/
theorem source_ports {F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (r : NP6_StdModel.Reservation) (H : Bytes → State) :
    S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (configuration c err r H))
      (first c err r H) (second c err r H) (F3U_Oracle.hashv H) ∧
    S2W_ExtractionBoundary.P1 H H ∧
    S2W_ExtractionBoundary.RuntimeSyscall (F3U_Oracle.hashv H) H ∧
    OraclePortCompactDraft.parse JFz_RowGeometry.wire =
      some ⟨JFz_RowGeometry.wire,JFz_Parsed.rows00⟩ := by
  refine ⟨⟨by intros; rfl,by intros; rfl,by intros; rfl⟩,
    ⟨fun _ => rfl⟩,F3U_Oracle.syscall H,JFz_Parsed.parsed⟩

#print axioms source_ports
end AspisR1.JFz_SourceAssociation
end
