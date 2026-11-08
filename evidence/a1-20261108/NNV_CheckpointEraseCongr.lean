import NNV_CheckpointValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_CheckpointEraseCongr
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

theorem source {A H : Type} (first second : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (code : Code A)
 (same : ∀ parts, first.digest hash parts = second.digest hash parts) :
 erase first hash code = erase second hash code := by
 induction code with
 | done value => rfl
 | step r k ih =>
  change (r >>= fun x => erase first hash (k x)) = (r >>= fun x => erase second hash (k x))
  exact congrArg (fun f => r >>= f) (funext ih)
 | read parts k ih =>
  change (first.digest hash parts >>= fun x => erase first hash (k x)) =
   (second.digest hash parts >>= fun x => erase second hash (k x))
  rw [same]
  exact congrArg (fun f => second.digest hash parts >>= f) (funext ih)
#print axioms source
end AspisR1.NNV_CheckpointEraseCongr
end
