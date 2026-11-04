import PV_2TNV_SourceBytes
import R1Z.PrivacyR1HeadlineDeployedReal
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_HeadlineFibre
open R1Z PV_2TNV_PublicEncoding
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P
abbrev H := PhaseWireLog2Bin.honest PrivacyR1HeadlineDeployedReal.input

def witness : H.Instance := PV_2TNV_CanonicalWitness.witness

theorem public_eq {CommitHandle : Type} (handle : CommitHandle) :
    H.public witness = (x handle).1 := rfl

theorem fibre {CommitHandle : Type} (handle : CommitHandle) :
    ∃ w : H.Instance, H.public w = (x handle).1 := ⟨witness,public_eq handle⟩

#print axioms witness
#print axioms public_eq
#print axioms fibre
end AspisR1.PV_2TNV_HeadlineFibre
