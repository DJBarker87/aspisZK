import R1Z.PV_RunJoin_PreparedActual48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PreparedFields48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_PreparedDomain48 (W Domain)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa alpha0 : W) (c0bytes : alloc.vec.Vec U8)
    (q1 w1 : alloc.vec.Vec W) (domain : Domain) (out : prover.PreparedOpening)
    (h : @PV_RunJoin_PreparedDomain48.run (types base) (selected base heap box ops)
      backend sem transcript y1 gamma inactive kappa alpha0 c0bytes q1 w1 domain=ok (.Ok out)) :
    ∃ folded, domain=ok (.Ok folded) ∧
      out.backend=backend ∧ out.sem=sem ∧ out.transcript=transcript ∧ out.y1=y1 ∧
      out.gamma=gamma ∧ out.inactive=inactive ∧ out.kappa=kappa ∧ out.alpha0=alpha0 ∧
      out.c0bytes=c0bytes ∧ out.q1=q1 ∧ out.w1=w1 ∧ out.folded_word=folded := by
  rw [PV_RunJoin_PreparedActual48.complete base heap box ops] at h
  cases domain with
  | fail e => cases h
  | div => cases h
  | ok status =>
    cases status with
    | Err e => cases h
    | Ok folded =>
      have same := core.result.Result.Ok.inj (Result.ok.inj h)
      cases same
      exact ⟨folded,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms complete
end R1Z.PV_RunJoin_PreparedFields48
