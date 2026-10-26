import FIp_CircleQuery
import FIp_DotsAdapter
import FIp_Equality
import FIp_SemanticArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_Install
open Aeneas Aeneas.Std Result DrvC_Installation

def select {C : Type} (r : NP6_StdModel.Reservation) (c : Configuration FIo_Install.W C) : Configuration FIo_Install.W C :=
  {FIo_Install.select r c with
    query:={c.query with op20:=FIp_DotsAdapter.dots,op17:=FIp_CircleQuery.circle,widePartialEq:=FIp_Equality.dictionary}
    boundaries:=FIp_SemanticArithmetic.install c.boundaries}

def configuration {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) := Rc5_Install.configuration err (select r c) r

theorem slots {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation) :
    (configuration err c r).query.op17=FIp_CircleQuery.circle ∧
    (configuration err c r).query.widePartialEq=FIp_Equality.dictionary ∧
    (configuration err c r).query.op20=FIp_DotsAdapter.dots ∧
    (configuration err c r).boundaries.mask=FIp_SemanticArithmetic.mask ∧
    (configuration err c r).boundaries.add=FIp_SemanticArithmetic.add ∧
    (configuration err c r).boundaries.mul=FIp_SemanticArithmetic.mul ∧
    (configuration err c r).boundaries.terminal=c.boundaries.terminal := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms slots
end AspisR1.FIp_Install
end
