import NMX_R4_ReadDecode
set_option autoImplicit false
noncomputable section
namespace NMX_R4_BoxProjection
open RSL NMX_R4_AccountProjection

theorem master {B : Type} (a : OwnedAccount) (k : Master → RS B) :
 RS.bind (account a).data (fun b => RS.bind (decodeMasterBox LIBB_PoolLib.library b) k) =
 RS.bind a.data (fun b => RS.bind (decodeMasterBox LIBB_PoolLib.library b) k) :=
 NMX_R4_ReadDecode.boxed LIBB_PoolLib.library.decodeMaster NMX_R4_ByteCut.master a k

theorem checkpoint {B : Type} (a : OwnedAccount) (k : Checkpoint → RS B) :
 RS.bind (account a).data (fun b => RS.bind (decodeCheckpointBox LIBB_PoolLib.library b) k) =
 RS.bind a.data (fun b => RS.bind (decodeCheckpointBox LIBB_PoolLib.library b) k) :=
 NMX_R4_ReadDecode.boxed LIBB_PoolLib.library.decodeCheckpoint NMX_R4_ByteCut.checkpoint a k

theorem key (a : OwnedAccount) : (account a).key = a.key := rfl
#print axioms master
#print axioms checkpoint
#print axioms key
end NMX_R4_BoxProjection
end
