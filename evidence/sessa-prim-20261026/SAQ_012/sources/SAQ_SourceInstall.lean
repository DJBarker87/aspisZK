import Rc2_Install
import SAQ_QuerySource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_SourceInstall
/-- Instantiate only the scalar query slots of the actual Rc2 configuration. -/
def select {F C : Type} (c : DrvC_Installation.Configuration F C) :
    DrvC_Installation.Configuration F C :=
  {c with query := SAQ_QuerySource.install c.query}

def configuration {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :=
  Rc2_Install.configuration (select c) reservation

theorem query {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    (configuration c reservation).query=SAQ_QuerySource.install c.query := rfl

theorem primitives {F C : Type} (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation)
    (rest : SAQ_QuerySource.Remaining (configuration c reservation).query) :
    Port5Q1_QueryPorts.SessionAPrimitives (configuration c reservation).query :=
  SAQ_QuerySource.primitives c.query rest

theorem idempotent {F C : Type} (c : DrvC_Installation.Configuration F C) :
    select (select c)=select c := rfl

#print axioms query
#print axioms primitives
#print axioms idempotent
end AspisR1.SAQ_SourceInstall
end
