import NMX_Semantics
import NMX_HeterogeneousPrimitives
import NMX_PdaSound
set_option autoImplicit false
noncomputable section
namespace NMX_CommandTransport
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel
open NMX_Carrier

theorem thrown {A B : Type} (encode : A → B) (e : RSL.ProgramError) :
 NMX_Heterogeneous.Refines encode (RSL.RS.throw e) (RSL.RS.throw e) := by
 intro env o run
 change o = ⟨.ret (.error e),[]⟩ at run
 subst o
 rfl

theorem data (owners : Owners) (lane : NMX_RawChildren.LaneNative)
 (registry : NMX_RawChildren.RegistryNative) (a : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Heterogeneous.Refines bytes (NMX_Semantics.command owners lane registry (.data a))
  (RSL.RS.ofExcept (RSL.OwnedAccount.data (account a))) := by
 unfold NMX_Semantics.command RSL.OwnedAccount.data account
 cases h : a.bytes with
 | Ok v => exact NMX_HeterogeneousPrimitives.pure bytes v.deref
 | Err e => exact thrown bytes (error e)

theorem pda (owners : Owners) (lane : NMX_RawChildren.LaneNative)
 (registry : NMX_RawChildren.RegistryNative) (seeds : Slice (Slice U8)) (program : solana_pubkey.Pubkey) :
 NMX_Heterogeneous.Refines key (NMX_Semantics.command owners lane registry (.pda seeds program))
  (RSL.pdaOrErr (seeds.val.map bytes) (key program)) := by
 intro env o run
 unfold NMX_Semantics.command at run
 subst o
 have law := NMX_PdaSound.observation (seeds.val.map bytes) (key program) env
 convert law using 1
 cases reply : env.pda (seeds.val.map bytes) (key program) with
 | none => rfl
 | some output => simp only [NMX_RawChildren.mapObs,NMX_InverseBytes.key_roundtrip]

theorem lane (owners : Owners) (native : NMX_RawChildren.LaneNative)
 (registry : NMX_RawChildren.RegistryNative)
 (packet : NMX_RawChildren.RowSpec_217 native) (b : Slice U8) :
 NMX_Heterogeneous.Refines (fun box : Box Lane => NMX_Carrier.lane box.payload)
  (NMX_Semantics.command owners native registry (.lane b))
  (RSL.Spec.call RSL.TX2_217.Domain RSL.TX2_217.Ref (bytes b)) := by
 intro env o run
 change o = native b env at run
 subst o
 exact ⟨True.intro,packet b env⟩

theorem registry (owners : Owners) (nativeLane : NMX_RawChildren.LaneNative)
 (native : NMX_RawChildren.RegistryNative) (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (packet : NMX_RawChildren.RowSpec_234 L D native)
 (v p : solana_pubkey.Pubkey) (ma : r1_pool_adapter.owned.OwnedAccount) (m : Master)
 (r e : r1_pool_adapter.owned.OwnedAccount) (slot : U64) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.command owners nativeLane native (.registry v p ma m r e slot))
  (RSL.Spec.call RSL.TX2_234.Domain (RSL.TX2_234.Ref L D)
   (NMX_CallArguments.registry v p ma m r e slot)) := by
 intro env o run
 change o = native ⟨v,p,ma,m,r,e,slot⟩ env at run
 subst o
 rw [NMX_HeterogeneousPrimitives.map_identity]
 exact ⟨True.intro,packet _ env⟩
#print axioms thrown
#print axioms data
#print axioms pda
#print axioms lane
#print axioms registry
end NMX_CommandTransport
end
