import Rc3_Install
import SAQ_CompleteInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc4_Install
open DrvC_Installation

def select {F C : Type} (err : C) (c : Configuration F C) :=
  SAQ_CompleteInstall.select err c

def configuration {F C : Type} (err : C) (c : Configuration F C)
    (r : NP6_StdModel.Reservation) := Rc3_Install.configuration (select err c) r

theorem rc3 {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    configuration err c r = Rc3_Install.configuration (SAQ_CompleteInstall.select err c) r := rfl

theorem saq {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    configuration err c r = SAQ_CompleteInstall.configuration err
      {c with boundaries:=F3M_CircleSource.install c.boundaries} r := rfl

theorem query {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    (configuration err c r).query=SAQ_Decoder.install c.query := rfl

theorem geometry {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    (configuration err c r).geometry=SAQ_Constructor.install err c.geometry := rfl

theorem exact_scope {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    configuration err c r = Rc3_Install.configuration c r ↔
      SAQ_Decoder.install c.query=c.query ∧ SAQ_Constructor.install err c.geometry=c.geometry := by
  constructor
  · intro h
    exact ⟨congrArg Configuration.query h,congrArg Configuration.geometry h⟩
  · rintro ⟨hq,hg⟩
    change Rc3_Install.configuration (SAQ_CompleteInstall.select err c) r = _
    have seed : SAQ_CompleteInstall.select err c=c := by
      unfold SAQ_CompleteInstall.select
      rw [hq,hg]
    rw [seed]

#print axioms rc3
#print axioms saq
#print axioms query
#print axioms geometry
#print axioms exact_scope
end AspisR1.Rc4_Install
end
