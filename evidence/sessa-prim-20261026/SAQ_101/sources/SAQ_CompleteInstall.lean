import Rc2_Install
import SAQ_Decoder
import SAQ_Constructor
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_CompleteInstall

def select {F C : Type} (indexError : C) (c : DrvC_Installation.Configuration F C) :
    DrvC_Installation.Configuration F C :=
  {c with query := SAQ_Decoder.install c.query, geometry := SAQ_Constructor.install indexError c.geometry}

def configuration {F C : Type} (indexError : C) (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) := Rc2_Install.configuration (select indexError c) reservation

theorem primitives {F C : Type} (indexError : C) (c : DrvC_Installation.Configuration F C)
    (reservation : NP6_StdModel.Reservation) :
    Port5Q1_QueryPorts.SessionAPrimitives (configuration indexError c reservation).query :=
  SAQ_Decoder.primitives c.query

#print axioms primitives
end AspisR1.SAQ_CompleteInstall
end
