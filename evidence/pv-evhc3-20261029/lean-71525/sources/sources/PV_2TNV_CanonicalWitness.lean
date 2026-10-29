import PV_2TNV_TransferCore
import PV_2TNV_AppendBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_CanonicalWitness
open R1Z PV_2TNV_PublicEncoding
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

def witness : BuilderCanonical.Instance (K := K) :=
  ⟨(nativePublic,PV_RunJoin_FixtureRecords.witness false),
    PV_RunJoin_FixtureFibres.lift_spendPlus _ _
      (PV_2TNV_TransferCore.spendPlus PV_2TNV_AppendBinding.source)⟩

theorem public_eq {CommitHandle : Type} (handle : CommitHandle) :
    (BuilderSource.prover (K := K)).public witness = (x handle).1 := rfl

theorem fibre {CommitHandle : Type} (handle : CommitHandle) :
    ∃ w : (BuilderSource.prover (K := K)).Instance,
      (BuilderSource.prover (K := K)).public w = (x handle).1 := ⟨witness,public_eq handle⟩

#print axioms witness
#print axioms public_eq
#print axioms fibre
end AspisR1.PV_2TNV_CanonicalWitness
