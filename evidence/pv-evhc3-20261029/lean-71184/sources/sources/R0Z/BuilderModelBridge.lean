import R0Z.BuilderComplete
import R0Z.BuilderModelAux
import R0Z.BuilderModelDigest
import R0Z.BuilderModelSentinel

/-! The builder model against `BuilderComplete` (t2b2b/DESIGN-BUILDER-MODEL.txt §4, §5).

* `nonCopy_model`: `NonCopyHolds pub (buildModel pub w)` from the aux and
  digest premises — the first field of `BuilderRefines` for the model.
* `refines_forces_sentinel`: whatever the builder, `BuilderRefines S Rel`
  forces `pub.change 7 ≠ 0` on every transfer instance of `Rel`; hence the
  relation to instantiate is Rspend strengthened by the non-zero change
  sentinel (the Rust retry condition), not Rspend itself. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.BuilderModel
open R0P R0Z.BuilderComplete

variable {K : Type} [Field K]

theorem nonCopy_model [CharP K 0x7fffffff] (pub : Public K) (w : ModelWitness K)
    (hA : AuxPremises pub w) (hD : DigestPremises pub w) : NonCopyHolds pub (buildModel pub w) :=
  ⟨value_model pub w hA.conservation, occupancy_model pub w hA, asset_model pub w hA.amount,
    schedule_model pub w, path_model pub w, digest_model pub w hD, poseidon_model pub w⟩

theorem refines_forces_sentinel [Fintype K] [DecidableEq K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K} {W : Type}
    (S : BuilderSpec F W) (Rel : Public K → W → Prop) (hR : BuilderRefines S Rel)
    (pub : Public K) (w : W) (hw : Rel pub w) (hv : pub.variant = .privateTransfer) :
    pub.change 7 ≠ 0 := by
  obtain ⟨_, ho, _, _, _, hd, _⟩ := hR.nonCopy pub w hw
  exact change_sentinel_of_balance pub _ ho hd (hR.balance pub w hw) hv

#print axioms nonCopy_model
#print axioms refines_forces_sentinel
end R0Z.BuilderModel
