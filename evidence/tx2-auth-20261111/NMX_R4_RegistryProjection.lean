import NMX_R4_AccountProjection
import NMX_R3_RegistryProjectionRef
set_option autoImplicit false
noncomputable section
namespace NMX_R4_RegistryProjection
open RSL RSL.TX2_234
open NMX_R4_AccountProjection (account)

theorem cut_idem (b : Bytes) :
 NMX_R3_RegistryByteCut.cut (NMX_R3_RegistryByteCut.cut b) = NMX_R3_RegistryByteCut.cut b := by
 change (if (NMX_R3_RegistryByteCut.cut b).length ≤ Aeneas.Std.Usize.max then NMX_R3_RegistryByteCut.cut b else []) = NMX_R3_RegistryByteCut.cut b
 rw [if_pos (NMX_R3_RegistryByteCut.bound b)]

theorem account_same (a : OwnedAccount) :
 NMX_R3_RegistryProjection.account (account a) = NMX_R3_RegistryProjection.account a := by
 cases a with
 | mk key owner sign write exec len bytes =>
  cases bytes <;> simp only [NMX_R3_RegistryProjection.account,account,Except.map,cut_idem]

def args (a : Args) : Args :=
 {a with master_account := account a.master_account,
         registry_account := account a.registry_account,
         entry_account := account a.entry_account}

theorem same (a : Args) :
 NMX_R3_RegistryProjection.args (args a) = NMX_R3_RegistryProjection.args a := by
 simp only [NMX_R3_RegistryProjection.args,args,account_same]

theorem reference (D : DeployedIds) (a : Args) :
 Ref LIBB_PoolLib.library D (args a) = Ref LIBB_PoolLib.library D a := by
 rw [← NMX_R3_RegistryProjectionRef.reference D (args a),same,
     NMX_R3_RegistryProjectionRef.reference]
#print axioms cut_idem
#print axioms account_same
#print axioms same
#print axioms reference
end NMX_R4_RegistryProjection
end
