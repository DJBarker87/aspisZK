import R1Z.PV_RunJoin_ClaimProducer48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimProducerCongruence50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ClaimThread48 (Column W)

theorem complete (f g : Column → Result W) (equal : ∀ q,f q=g q)
    (columns : List Column) (out : alloc.vec.Vec U8) :
    PV_RunJoin_ClaimProducer48.run f columns out=PV_RunJoin_ClaimProducer48.run g columns out := by
  induction columns generalizing out with
  | nil => rfl
  | cons q tail ih =>
    simp only [PV_RunJoin_ClaimProducer48.run,equal,ih]
#print axioms complete
end R1Z.PV_RunJoin_ClaimProducerCongruence50
