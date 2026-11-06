import NLM_Auth064Domain
set_option autoImplicit false
noncomputable section
namespace NLM_Auth064
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes
/-- Actual child reference, not a separately selected observation/result. -/
def reference {Ambient : Type} (wr rr : NP6_StdModel.Reservation)
 (merkle : NJJ_Common.Merkle) (finish : NJJ_Common.Finish) : NLM_RowSpec_065.Native Ambient :=
 fun f world => ⟨world,NJU_CommonObserved.run wr rr merkle finish f.digest
   f.publicBytes f.proof f.checkpoint f.hash none⟩
/-- Intermediate (bd) fold only: the full OPEN065 packet is consumed at
SAME arguments after deriving its actual native size domain internally.
This is not a positive row root; parent-native cut installation is pending. -/
theorem parameterized_fold {Ambient H : Type} (common : NLM_RowSpec_065.Native Ambient)
 (wr rr : NP6_StdModel.Reservation) (merkle : NJJ_Common.Merkle) (finish : NJJ_Common.Finish)
 (packet : NLM_RowSpec_065.RowSpec_065 common wr rr merkle finish)
 (s : State Ambient H) : G common s=G (reference wr rr merkle finish) s := by
 unfold G
 cases parsed : NLE_ParseInstall.parse s.input.proof with
 | fail err => rfl
 | div => rfl
 | ok result =>
   cases result with
   | Err err => rfl
   | Ok variant =>
     have same := (packet (commonFrame {s with parsed:=some variant}) s.world
       (child_domain s variant parsed)).1
     dsimp only at same ⊢
     rw [same]
     rfl
#print parameterized_fold
#print axioms parameterized_fold
end NLM_Auth064
