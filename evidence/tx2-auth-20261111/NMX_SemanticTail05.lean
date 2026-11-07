import NMX_SF05
import NMX_CB05
import NMX_BoxCommands
import NMX_DenoteStep
set_option autoImplicit false
noncomputable section
namespace NMX_SemanticTail05
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier

theorem e055 (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (m : Box Master) (c : Box Checkpoint) (l : Box Lane) (lk : solana_pubkey.Pubkey)
 (live : Box Snapshot) (mb cb : Array U8 32#usize) :
 NMX_Heterogeneous.Refines id
 (NMX_Semantics.denote owners ln rn (NMX_SF05.p055 m c l lk live mb cb))
 (NMX_CB05.r055 L D (master m.payload) (checkpoint c.payload) (lane l.payload)
  (key lk) (snapshot live.payload) (key mb) (key cb)) := by
 unfold NMX_SF05.p055 NMX_CB05.r055
 rw [NMX_DenoteStep.call]
 apply NMX_Heterogeneous.bind key id
 · exact NMX_HeterogeneousPrimitives.pure key lk
 · intro result
   exact NMX_HeterogeneousPrimitives.pure id _

#print axioms e055
end NMX_SemanticTail05
end
