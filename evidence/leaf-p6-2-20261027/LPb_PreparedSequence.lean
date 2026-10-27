import LPb_ClaimStages
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace LPb_PreparedSequence
/-- Same model, factored stages; not a native-source equivalence theorem. -/
def sequence {H : Type} (_ : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (inactive : XRk_Wide)
    (g : Array XRk_Wide 29#usize) (kappa : XRk_Wide) :
    Result (core.result.Result XRk_Wide verifier.Error) := do
  let one ← aspis_core.field.wide_exact.WideExact.ONE
  let zero ← aspis_core.field.wide_exact.WideExact.ZERO
  let powers ← XRk_powers kappa 7 one
  let parts ← (List.range 6).foldlM (fun (parts : Option (List XRk_Wide)) point => do
    match parts with
    | none => ok none
    | some parts =>
      let p ← LPb_ClaimStages.sequence sem y1 g point
      ok (p.map (fun p => parts ++ [p]))) (some [])
  match parts with
  | none => ok (.Err .Parse)
  | some parts => do
    let parts := inactive :: parts
    let result ← (powers.zip parts).foldlM (fun sum (k,p) => do
      let term ← aspis_core.field.wide_exact.WideExact.mul k p
      aspis_core.field.wide_exact.WideExact.add sum term) zero
    ok (.Ok result)

theorem prepared_model_stages {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (inactive : XRk_Wide)
    (g : Array XRk_Wide 29#usize) (kappa : XRk_Wide) :
    verifier.prepared_claim D sem y1 inactive g kappa = sequence D sem y1 inactive g kappa := rfl
#print axioms prepared_model_stages
end LPb_PreparedSequence
