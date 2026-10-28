import JHv_Configuration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_ConfigAdapter
open Aeneas Aeneas.Std Result DrvC_Installation
open JHv_Configuration

theorem key : JHd_KeyStd.keyEq=Hist_Authority.keyEq :=
  funext (fun a=>funext (fun b=>JHf_KeyEq.key a b))
#print axioms key

/-- Only the adapter projection is reduced; the heavy verifier/configuration
fields are kept outside this dictionary normalization. -/
theorem source (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    (prepare (seed base stage)).adapter=(seed base stage).adapter := by
  change {JHd_ReferenceSlots.install (seed base stage).adapter with
    op19:=ok 1520#usize,op43:=S2W_DigestExtraction.digest (F3U_Oracle.hashv JFp_SHADigest.digest),
    op51:=JHf_Scan.source,op52:=JHf_ReconstructionSlot.source,op53:=JHb_EmitAdapter.source}=
    (seed base stage).adapter
  unfold JHd_ReferenceSlots.install JHd_KeyStd.install
  rw [key]
  exact Eq.refl _
#print axioms source
end AspisR1.JHv_ConfigAdapter
end
