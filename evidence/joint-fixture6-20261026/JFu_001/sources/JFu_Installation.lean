import Rc7_Top
import F3U_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_Installation
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def seed {F C : Type} (c : DrvC_Installation.Configuration F C) (H : Bytes → State) :=
  {c with adapter := {c.adapter with op43:=S2W_DigestExtraction.digest (F3U_Oracle.hashv H)}}
def configuration {F C : Type} (c : DrvC_Installation.Configuration F C) (err : C) (H : Bytes → State) :=
  Rc5_Install.configuration err (seed c H) (.Ok ())
def first {F C : Type} (c : DrvC_Installation.Configuration F C) (err : C) (H : Bytes → State) :=
  AdapterRw.r1_pool_adapter.owned.stage1_owned (DrvC_Installation.sdk (configuration c err H))
def second {F C : Type} (c : DrvC_Installation.Configuration F C) (err : C) (H : Bytes → State) :=
  AdapterRw.r1_pool_adapter.owned.stage2_owned (DrvC_Installation.sdk (configuration c err H))

theorem extraction {F C : Type} (c : DrvC_Installation.Configuration F C) (err : C) (H : Bytes → State) :
    S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (configuration c err H))
      (first c err H) (second c err H) (F3U_Oracle.hashv H) :=
  ⟨by intros;rfl,by intros;rfl,by intros;rfl⟩

theorem oracle (H : Bytes → State) : S2W_ExtractionBoundary.P1 H H ∧
    S2W_ExtractionBoundary.RuntimeSyscall (F3U_Oracle.hashv H) H :=
  ⟨⟨fun _ => rfl⟩,F3U_Oracle.syscall H⟩

#print axioms extraction
#print axioms oracle
end AspisR1.JFu_Installation
end
