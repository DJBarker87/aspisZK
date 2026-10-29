import R1Z.PV_RunJoin_QueryAccess64
import R1Z.PV_RunJoin_QueryHead63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QuerySaltTotal64
attribute [local irreducible] PV_RunJoin_WeightInstalled46.selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (c : host_commitment.Commitment)
    (salts : host_commitment.PrivateSalts) (stored : c.private_salts=some salts)
    (length : 262144≤salts.length) (u : aspis_core.r0.domain.FibreIndex)
    (bound : u.val<262144) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∃ salt, host_commitment.Commitment.opening_salt c u=ok (some salt) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨salt,hs⟩ := PV_RunJoin_QueryAccess64.salt salts u (by omega)
  refine ⟨salt,?_⟩
  unfold host_commitment.Commitment.opening_salt
  rw [stored]
  change (do let i ← (selected base heap box ops).op76 u
             let a ← host_commitment.PrivateSalts.get salts i
             ok (some a))=_
  rw [PV_RunJoin_QueryHead63.get]
  simp only [ProverRwDictionaryDomain.fibreGet,bind_tc_ok,hs]

#print axioms complete
end R1Z.PV_RunJoin_QuerySaltTotal64
