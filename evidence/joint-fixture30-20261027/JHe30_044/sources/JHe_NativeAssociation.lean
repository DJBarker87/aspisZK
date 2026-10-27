import JHe_CurrentAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_NativeAssociation
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem self_update (ops : Ops) : {ops with op16:=@ops.op16}=ops := by
  cases ops
  rfl
#print axioms self_update

theorem source (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    DrvC_Installation.currentInstalled (JHe_Configuration.value adapter stage)=
      {JGr_Geometry.installed with op16:=Tx1Q_Install.writer} := by
  let actual := DrvC_Installation.currentInstalled (JHe_Configuration.value adapter stage)
  have writer : @actual.op16=@Tx1Q_Install.writer := rfl
  have transport := congrArg (fun ops : Ops=>{ops with op16:=Tx1Q_Install.writer})
    (JHe_CurrentAssociation.source adapter stage)
  change {actual with op16:=Tx1Q_Install.writer}={JGr_Geometry.installed with op16:=Tx1Q_Install.writer} at transport
  have same : {actual with op16:=Tx1Q_Install.writer}=actual := by
    rw [←writer]
    exact self_update actual
  exact same.symm.trans transport
#print axioms source
end AspisR1.JHe_NativeAssociation
end
