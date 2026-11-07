import NMX_R2_Semantics
import NMX_R2_CloneTransport
import NMX_R2_HeterogeneousPrimitives
import NMX_R2_PdaSound
set_option autoImplicit false
noncomputable section
namespace NMX_R2_CommandTransport
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel
open NMX_R2_Carrier

theorem thrown {A B : Type} (encode : A → B) (e : RSL.ProgramError) :
 NMX_R2_Heterogeneous.Refines encode (RSL.RS.throw e) (RSL.RS.throw e) := by
 intro env o run
 change o = ⟨.ret (.error e),[]⟩ at run
 subst o
 rfl

theorem data (owners : Owners) (lane : NMX_R2_RawChildren.LaneNative)
 (registry : NMX_R2_RawChildren.RegistryNative) (a : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R2_Heterogeneous.Refines bytes (NMX_R2_Semantics.command owners lane registry (.data a))
  (RSL.OwnedAccount.data (account a)) := by
 change NMX_R2_Heterogeneous.Refines bytes
  (RSL.RS.ofCloned (reply (fun v => v.deref) a.bytes))
  (RSL.RS.ofCloned (reply (fun v => v.val.map byte) a.bytes))
 cases h : a.bytes with
 | Ok v => exact NMX_R2_HeterogeneousPrimitives.pure bytes v.deref
 | Err e => exact NMX_R2_CloneTransport.error bytes (error e)

theorem pda (owners : Owners) (lane : NMX_R2_RawChildren.LaneNative)
 (registry : NMX_R2_RawChildren.RegistryNative) (seeds : Slice (Slice U8)) (program : solana_pubkey.Pubkey) :
 NMX_R2_Heterogeneous.Refines key (NMX_R2_Semantics.command owners lane registry (.pda seeds program))
  (RSL.pdaOrErr (seeds.val.map bytes) (key program)) := by
 intro env o run
 unfold NMX_R2_Semantics.command at run
 subst o
 have law := NMX_R2_PdaSound.observation (seeds.val.map bytes) (key program) env
 convert law using 1
 cases reply : env.pda (seeds.val.map bytes) (key program) with
 | none => rfl
 | some output => simp only [NMX_R2_RawChildren.mapObs,NMX_R2_InverseBytes.key_roundtrip]

theorem lane (owners : Owners) (native : NMX_R2_RawChildren.LaneNative)
 (registry : NMX_R2_RawChildren.RegistryNative)
 (packet : NMX_R2_RawChildren.RowSpec_217 native) (b : Slice U8) :
 NMX_R2_Heterogeneous.Refines (fun box : Box Lane => NMX_R2_Carrier.lane box.payload)
  (NMX_R2_Semantics.command owners native registry (.lane b))
  (RSL.Spec.call RSL.TX2_217.Domain RSL.TX2_217.Ref (bytes b)) := by
 intro env o run
 change o = native b env at run
 subst o
 exact ⟨True.intro,packet b env⟩

#print axioms thrown
#print axioms data
#print axioms pda
#print axioms lane
end NMX_R2_CommandTransport
end
