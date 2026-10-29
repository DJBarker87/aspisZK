import R1Z.PV_RunJoin_PreparedMapErr48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PreparedActual48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_PreparedDomain48 (W Domain)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (transcript : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa alpha0 : W) (c0bytes : alloc.vec.Vec U8)
    (q1 w1 : alloc.vec.Vec W) (domain : Domain) :
    @PV_RunJoin_PreparedDomain48.run (types base) (selected base heap box ops)
      backend sem transcript y1 gamma inactive kappa alpha0 c0bytes q1 w1 domain=
      match domain with
      | fail e => fail e
      | div => div
      | ok (.Err _) => ok (.Err verifier.Error.Allocation)
      | ok (.Ok folded) => ok (.Ok {backend,sem,transcript,y1,gamma,inactive,kappa,alpha0,c0bytes,q1,w1,folded_word:=folded}) := by
  cases domain with
  | fail e => rfl
  | div => rfl
  | ok status =>
    cases status with
    | Ok folded =>
      simp only [PV_RunJoin_PreparedDomain48.run,bind_tc_ok,
        PV_RunJoin_PreparedMapErr48.success base heap box ops,
        PV_RunJoin_PreparedDomain48.success]
    | Err e =>
      simp only [PV_RunJoin_PreparedDomain48.run,bind_tc_ok,
        PV_RunJoin_PreparedMapErr48.error base heap box ops,
        PV_RunJoin_PreparedDomain48.inner_error]
#print axioms complete
end R1Z.PV_RunJoin_PreparedActual48
