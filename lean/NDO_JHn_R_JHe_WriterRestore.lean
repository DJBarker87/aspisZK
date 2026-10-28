import NDO_JHn_R_JHe_WriterCommutation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_WriterRestore
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem source (actual content : Ops)
    (same : {actual with op16:=WAdm_Install.writer}=content)
    (writer : @actual.op16=@Tx1Q_Install.writer) :
    actual={content with op16:=Tx1Q_Install.writer} := by
  have transport := congrArg (fun ops : Ops=>{ops with op16:=Tx1Q_Install.writer}) same
  change {actual with op16:=Tx1Q_Install.writer}={content with op16:=Tx1Q_Install.writer} at transport
  have identity : {actual with op16:=Tx1Q_Install.writer}=actual := by
    rw [←writer]
  exact identity.symm.trans transport
#print axioms source
end AspisR1.JHe_WriterRestore
end
