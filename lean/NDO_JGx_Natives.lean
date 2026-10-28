import NDO_JGx_Configuration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Natives
open Aeneas Aeneas.Std Result DrvC_Installation

def first {C : Type} (c : Configuration FIo_Install.W C) (err : C) : S2W_ExtractionBoundary.First :=
  AdapterRw.r1_pool_adapter.owned.stage1_owned (DrvC_Installation.sdk (JGx_Configuration.value c err))

def second {C : Type} (c : Configuration FIo_Install.W C) (err : C) : S2W_ExtractionBoundary.Second :=
  AdapterRw.r1_pool_adapter.owned.stage2_owned (DrvC_Installation.sdk (JGx_Configuration.value c err))

theorem extraction {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (JGx_Configuration.value c err))
      (first c err) (second c err) (F3U_Oracle.hashv JFp_SHADigest.digest) :=
  ⟨by intros;rfl,by intros;rfl,by intros;rfl⟩
#print axioms extraction

theorem oracle : S2W_ExtractionBoundary.P1 JFp_SHADigest.digest JFp_SHADigest.digest ∧
    S2W_ExtractionBoundary.RuntimeSyscall (F3U_Oracle.hashv JFp_SHADigest.digest) JFp_SHADigest.digest :=
  ⟨⟨fun _=>rfl⟩,F3U_Oracle.syscall JFp_SHADigest.digest⟩
#print axioms oracle
end AspisR1.JGx_Natives
end
