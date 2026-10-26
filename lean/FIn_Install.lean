import FIn_Polynomial
import Rc5_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_Install
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish

/-- Arithmetic/parser/dot installation. The two pairing slots are still retained
from seed; this is deliberately not a claim of a complete shipped dictionary. -/
def finishOps {W : Type} (seed : FinishOps W) : FinishOps W :=
  {SAG_StageScale.install seed with
    field := FIn_Primitives.field
    add := FIn_Primitives.add
    polynomial := FIn_Polynomial.polynomial
    dot := SAG_DotClosed.source}

def select {W C : Type} (c : DrvC_Installation.Configuration W C) :=
  {c with finish := finishOps c.finish}

def configuration {W C : Type} (err : C) (c : DrvC_Installation.Configuration W C)
    (r : NP6_StdModel.Reservation) := Rc5_Install.configuration err (select c) r

theorem slots {W : Type} (seed : FinishOps W) :
    (finishOps seed).field = FIn_Primitives.field ∧
    (finishOps seed).add = FIn_Primitives.add ∧
    (finishOps seed).polynomial = FIn_Polynomial.polynomial ∧
    (finishOps seed).dot = SAG_DotClosed.source ∧
    (finishOps seed).newWeights = seed.newWeights ∧
    (finishOps seed).pair = seed.pair := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem finish {W C : Type} (err : C) (c : DrvC_Installation.Configuration W C)
    (r : NP6_StdModel.Reservation) :
    (configuration err c r).finish = finishOps c.finish := rfl

theorem idempotent {W : Type} (seed : FinishOps W) : finishOps (finishOps seed) = finishOps seed := rfl

theorem retained {W : Type} (seed : FinishOps W) :
    {finishOps seed with field := seed.field, add := seed.add,
      polynomial := seed.polynomial, dot := seed.dot,
      quarter := seed.quarter, mulM := seed.mulM} = seed := by
  cases seed
  rfl

#print axioms slots
#print axioms finish
#print axioms idempotent
#print axioms retained
end AspisR1.FIn_Install
end
