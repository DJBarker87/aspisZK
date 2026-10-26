import Rc2_Install
import SAQ_Query
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_Install
/-- Instantiate only the scalar query slots of the actual Rc2 configuration. -/
def select {F C : Type} (c : DrvC_Installation.Configuration F C) :
    DrvC_Installation.Configuration F C :=
  {c with query := SAQ_Query.install c.query}

def configuration {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :=
  Rc2_Install.configuration (select c) reservation

theorem query {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    (configuration c reservation).query=SAQ_Query.install c.query := rfl

theorem primitives {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation)
    (rest : SAQ_Query.Remaining (configuration c reservation).query) :
    Port5Q1_QueryPorts.SessionAPrimitives (configuration c reservation).query :=
  SAQ_Query.primitives c.query rest

theorem fixed {F C : Type} (c : DrvC_Installation.Configuration F C)
    (h : Port4C_BasisOuter.SessionABasis c.query) : select c=c := by
  have eq := SAQ_Query.fixed c.query h
  cases c
  simpa only [select] using congrArg
    (fun q => DrvC_Installation.Configuration.mk _ _ _ _ _ q _ _ _) eq

#print axioms query
#print axioms primitives
#print axioms fixed
end AspisR1.SAQ_Install
end
