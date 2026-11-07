import NNH_Stage1ProofDomain
import LIBC_CanonicalScan
set_option autoImplicit false
noncomputable section
namespace NNH_Stage1R4
open RSL NNH_Libraries

theorem produce (a : TX1_345.Args) (p pub ck : OwnedAccount) (saved : Bytes) (env : Env)
 (packet : NNH_Stage1Cut.Packet a p pub ck saved env) :
 VL.checkValuesDom (slice (slice packet.proof_data AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES) OFF_Y1 OFF_INACTIVE) := by
 obtain ⟨child⟩ := NNH_Stage1BodyChild.produce a p pub ck saved env packet
 apply LIBC_CanonicalScan.r4_value _ env []
 refine ⟨NNH_Stage1ProofDomain.extent a p pub ck saved env packet,?_⟩
 change (⟨.ret (.ok ()),[]⟩ : Obs (Except LIBC_CanonicalScan.VErr Unit))=
  ⟨.ret (LIBC_CanonicalScan.value (slice packet.proof_data AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES) env),[]⟩
 have scan : LIBC_CanonicalScan.value (slice packet.proof_data AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES) env=.ok () := child.scanned
 rw [scan]
#print axioms produce
end NNH_Stage1R4
