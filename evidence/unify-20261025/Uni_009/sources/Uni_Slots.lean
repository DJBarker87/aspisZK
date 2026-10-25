import Uni_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.Uni_Slots

/-- Stage shape/finish and concrete batch commute as full records. -/
theorem stage_commutes {F : Type} (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) :
    Tx2I_Install.stage (Op5T_Concrete.stage base) finish =
      Op5T_Concrete.stage (Tx2I_Install.stage base finish) := by
  cases base; rfl

/-- Every installed TX1 operation survives sdkOps' verifier installation. -/
theorem current_slots {C : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    let installed := RowShape_InstalledSlots.verifierOps (Uni_Install.current ops reserved query geo) B std
    installed.op3 = Op3I_Install.sourceBody ∧ installed.op4 = Op4P_Install.sourceBody ∧
    @installed.op6 = @Op5T_Install.currentBatch Port4B_Install.leaves ∧
    installed.op7 = Tx1Q_Install.query (Tx1Q_QueryBridge.leaves query) ∧
    @installed.op16 = @Tx1Q_Install.writer ∧ installed.op17 = Tx1Q_Install.flush ∧
    installed.op18 = Tx1Q_PrefixInstall.newPending reserved ∧
    installed.op19 = Tx1Q_PrefixInstall.geometryBody geo ∧
    installed.op20 = Tx1Q_PrefixInstall.initial reserved := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Every installed TX2 operation survives the authenticated child installation. -/
theorem stage_slots {F : Type} (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) :
    let installed := Tx2I_Install.stage (Op5T_Concrete.stage base) finish
    installed.op3 = Tx2I_Install.shape ∧
    @installed.op5 = @Op5T_Install.stageBatch Port4B_Install.leaves ∧
    installed.op19 = Port4D_FinishInstall.finish finish := by
  exact ⟨rfl,rfl,rfl⟩

#print axioms stage_commutes
#print axioms current_slots
#print axioms stage_slots
end AspisR1.Uni_Slots
end
