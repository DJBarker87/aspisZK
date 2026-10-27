import RPz7_Uni_Install
set_option autoImplicit false
namespace AspisR1.FJt_CurrentCode

theorem same {C : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C) :
    Uni_Install.current ops reserved query geo=
      Op3I_Install.install (Op4P_Install.install
        (Tx1Q_Execution.base (Op5T_Concrete.current ops) reserved query geo)) := by
  rw [Uni_Install.current,Uni_Install.base,Uni_Install.scan_batch,Uni_Install.prefix_batch]
#print axioms same
end AspisR1.FJt_CurrentCode
