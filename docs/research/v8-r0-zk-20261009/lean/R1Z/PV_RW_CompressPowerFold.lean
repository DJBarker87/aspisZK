import R1Z.PV_RW_CompressPowerStep
import R1Z.PV_RW_CompressClosedFold
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressPowerFold
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev Q := ProverRwFull.aspis_core.field.QM31

def powerRun (lambda : Q) : Nat → Q → Result Q
  | 0, power => ok power
  | n+1, power => do
    let next ← qMul power lambda
    powerRun lambda n next

theorem projection (values : List U32) (lambda out power : Q) :
    mapResult Prod.snd (PV_RW_CompressClosedFold.fold values lambda (out,power))=
      powerRun lambda values.length power := by
  induction values generalizing out power with
  | nil => rfl
  | cons value tail ih =>
    obtain ⟨nextOut,nextPower,hs,hp⟩ := PV_RW_CompressPowerStep.image out power value lambda
    change mapResult Prod.snd (do
      let next ← PV_RW_CompressConcrete.step out power value lambda
      PV_RW_CompressClosedFold.fold tail lambda next)=(do
        let next ← qMul power lambda
        powerRun lambda tail.length next)
    rw [hs,hp]
    simpa only [bind_tc_ok] using ih nextOut nextPower
#print axioms projection
end R1Z.PV_RW_CompressPowerFold
