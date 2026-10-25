import Hiq_FirstHeader
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_InstalledHeader
open Aeneas Aeneas.Std Result DrvC_Installation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem decoded {F C : Type} (c : Configuration F C)
    (semantic : AdapterRw.LeadInputs.Public) (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (first : AdapterRw.first_decoded (sdk c) semantic pub proof split = ok (.Ok saved))
    (H : Bytes → State) (oracle : CheckpointBytes5Inputs.Oracle (S2Z.Oracle.leadDigest (sdk c)) () H) :
    CPhy_Header.decode (bytesOf saved.val) = some (H (bytesOf proof.val),H (bytesOf pub.val)) := by
  rw [cphy_dictionary,Uni_Install.compose_tx1] at first oracle
  exact Hiq_FirstHeader.decoded _ (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std
    semantic pub proof split saved first H oracle

#print axioms decoded
end AspisR1.Hiq_InstalledHeader
end
