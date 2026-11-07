import NNH_Tx2StdConfiguration
set_option autoImplicit false
noncomputable section
namespace NNH_DigestSource
open Aeneas Aeneas.Std AspisR1 AdapterRw

theorem value (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :
 SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_Tx2StdConfiguration.sdk missing env err reserve)=LIBB_PartitionEnv.digest env := by
 unfold SolanaDigest.Insts.Aspis_coreDigestDigest32 LIBB_PartitionEnv.digest
 congr 1
#print axioms value
end NNH_DigestSource
