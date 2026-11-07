import NMX_SemanticF00
import NMX_LengthGuard
import NMX_CanonicalCountFactor
import NMX_SyntaxFactor
set_option autoImplicit false
noncomputable section
namespace NMX_SevenSourceFold
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Carrier NMX_SourceModel
/-- Complete seven-account branch of the dictionary-free observation
interpretation. The original-list clause is discharged by the caller's count
branch. This is not a native RowSpec root or a std/runtime interpretation. -/
theorem fold (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount)
 (shape : accounts.val = [p,m,c,l,r,e,v]) :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_Skeleton.auth verifier accounts pool outputLane slot))
  (RSL.TX2_233.Ref (NMX_DecoderLibrary.install L) D
   ⟨key verifier,accounts.val.map account,key pool,byte outputLane,long slot⟩) := by
 have count : accounts.val.length = 7 := by simp only [shape,List.length_cons,List.length_nil]
 have scalarCount : Slice.len accounts = 7#usize := (NMX_LengthGuard.equal accounts).mpr count
 rw [NMX_SyntaxFactor.factor]
 simp only [scalarCount,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
 have canonical : NMX_CB00.r001 (NMX_DecoderLibrary.install L) D
   (key verifier) (accounts.val.map account) (key pool) (byte outputLane) (long slot) =
  RSL.TX2_233.Ref (NMX_DecoderLibrary.install L) D
   ⟨key verifier,accounts.val.map account,key pool,byte outputLane,long slot⟩ := by
  rw [shape]
  exact NMX_CanonicalCountFactor.seven _ _ _ _ _ _
   (account p) (account m) (account c) (account l) (account r) (account e) (account v)
 rw [← canonical]
 exact NMX_SemanticF00.e001 owners ln rn L D lanePacket registryPacket
  verifier accounts pool outputLane slot count
#print axioms fold
end NMX_SevenSourceFold
end
