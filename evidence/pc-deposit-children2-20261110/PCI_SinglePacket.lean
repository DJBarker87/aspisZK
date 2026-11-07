import PCI_SingleCohort
import PCI_DigestRoundtrip
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_SinglePacket
open PCA

def liftReply (reply : Result (Except LeafError PairWitness)) (state : PCA_State) : Result (Execution PairWitness) :=
 match reply with
 | .ok out => .ok ⟨state,[],match out with
     | .ok w => .ok w | .error e => .error (.leaf e)⟩
 | .fail e => .fail e
 | .div => .div

def reference (d : Digest) (state : PCA_State) : Result (Execution PairWitness) :=
 liftReply (do let out ← PCI_SingleRef.single_reference (PCI_DigestRoundtrip.encode d)
               ok (PCI_SingleCohort.decode out)) state

theorem full (d : Digest) (state : PCA_State) :
    reference d state=ok (PCC.singleOutputReference d state) := by
 unfold reference
 rw [PCI_SingleCohort.complete,PCI_DigestRoundtrip.roundtrip]
 change PCI_SingleComplete.observe d state= _
 exact PCI_SingleComplete.result_state_effects d state

#print axioms full
end PCI_SinglePacket
