import PCG_AddressRoots
set_option autoImplicit false
noncomputable section
namespace PCM_Inst_PdaSource
open Aeneas Aeneas.Std
abbrev StoredArgs := PCG_SdkPda.Request × PCG_AddressRoots.Key
/-- The exact CLOSED source model, preserving the ordered raw syscall request,
full reply, and stopped arm. The RSL.Env.pda carrier adapter remains OPEN. -/
def storedModel (a : StoredArgs) (op38 : PCG_AddressRoots.Op38) : PCG_AddressRoots.StoredObservation :=
 ⟨[a.1],do
   let reply ← PCG_SdkPda.createReply (op38 a.1)
   Result.ok (match reply with
    | .Ok address => decide (address.val = a.2.val)
    | .Err _ => false)⟩

def storedLaw (a : StoredArgs) (op38 : PCG_AddressRoots.Op38)
    (o : PCG_AddressRoots.StoredObservation) : Prop :=
 PCG_SdkPda.Domain a.1 ∧ o = storedModel a op38

theorem stored_root (a : StoredArgs) (op38 : PCG_AddressRoots.Op38)
    (domain : PCG_SdkPda.Domain a.1) :
    storedLaw a op38 (PCG_AddressRoots.nativeStored a.1 a.2 op38) :=
 ⟨domain,PCG_AddressRoots.row_379 a.1 a.2 op38 domain⟩

theorem stored_unique (a : StoredArgs) (op38 : PCG_AddressRoots.Op38)
    (domain : PCG_SdkPda.Domain a.1) : ∃ o, storedLaw a op38 o ∧ ∀ other, storedLaw a op38 other → other = o := by
 refine ⟨storedModel a op38,⟨domain,rfl⟩,?_⟩
 intro o h
 exact h.2

/-- The source root itself proves the request's original seed-domain clause;
it is not strengthened by this adapter or delegated as a success assumption. -/
theorem request_domain (program pool profile release : PCG_AddressRoots.Key)
    (op38 : PCG_AddressRoots.Op38) :
 PCG_SdkPda.Domain (PCG_RequestCarrier.request
   (PCG_AddressLaws.model_374 program pool profile release)) :=
 (PCG_AddressRoots.row_374 program pool profile release op38).2.1
#print axioms stored_root
#print axioms stored_unique
#print axioms request_domain
end PCM_Inst_PdaSource
end
