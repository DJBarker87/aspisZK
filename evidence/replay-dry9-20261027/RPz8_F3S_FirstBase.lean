import RPz8_F3S_Dictionary
set_option autoImplicit false
namespace AspisR1.F3S_FirstBase
 theorem preparation {C : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C) :
    Op5T_Concrete.current {GExp_FirstPair.base ops reserved query geo with op16:=Tx1Q_Install.writer}=
      Uni_Install.current ops reserved query geo := by
  cases ops
  rfl
#print axioms preparation
end AspisR1.F3S_FirstBase
