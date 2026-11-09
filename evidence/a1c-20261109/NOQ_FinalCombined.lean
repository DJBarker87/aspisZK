import NOM_TerminalDomain
import NOM_MerkleGuard
import NOM_MerkleVerify
import NOM_MerkleLoop
import NOM_MerkleParent
import NOM_FinalCombined
import NOC_FinishSource
import NOC_Op9Slot
import NOC_Op9
import NOC_MerkleBounded
import NOC_PrepareInventory
import NOC_PrepareDiv
import NOC_SlotAudit
import NOC_Run5bHost
import NOC_PrepareFront
import NOC_ReadTransport
import NOC_QueryLink
import NOC_QueryDomain
import NOC_ConvLeaves
import NOC_ConvSemantic
import NOC_Conv094
import NOC_Tx1Cut
import NOC_Tx1Forward
import NOC_Stage1Forward
import NOC_SemConv
import NOC_PrepareConv
import NOC_Tx1Conv
import NOC_Stage1Inv
import NOC_Stage1Conv
import NOC_Stage1Iff
import NOQ_WeakErrHost
import NOQ_A1Assembly
import NOQ_A1Converse
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOQ_FinalCombined
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_ReturnedCheckpoint

/-- The A1 model-transport field at the corrected host: NOQ_A1Assembly.field_of
applied to NOC_Stage1Iff.iff345 (a theorem with no hypotheses beyond its arguments).
No scaffold hypothesis remains. -/
def field {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) :
 RSL.TAS.NND_A1 (AspisR1.NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C :=
 NOQ_A1Assembly.field_of L0 copy std (fun c => AspisR1.NOC_Stage1Iff.iff345 c)

example {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) :
 type_of% (field (W := W) (Tx := Tx) L0 copy std) =
 RSL.TAS.NND_A1 (AspisR1.NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
  NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C := rfl

#print axioms field
#print axioms AspisR1.NOC_Stage1Iff.iff345
#print axioms NOQ_A1Assembly.field_of
end AspisR1.NOQ_FinalCombined
end
