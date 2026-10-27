import R1Z.PDict_Static222_Semantics
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
open Lean Elab Tactic

theorem erase_423 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base)
    (hw : @PDict_WorkTransport222.WorkExtensional base ops)
    (h12 : PDict_MapErrTransport222.MapErrLaw base ops) :
    letI : ExternalTypes := base
    ∀ {T : Type} (si : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (public1 : Public) (compiled : Compilation) (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (binding : Array U8 32#usize) (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s : T),
    @prover.prove_masked_with_attempt (types base F) (selected base F ops) T si
      (pub base F public1) (compilation base F compiled) variant hash context binding attempt s =
    @prover.prove_masked_with_attempt base ops T si
      public1 compiled variant hash context binding attempt s := by
  intro T si public1 compiled variant hash context binding attempt s
  delta prover.prove_masked_with_attempt
  run_tac do
    let env ← getEnv
    for (n, _) in env.constants.toList do
      if "ProverRwFull.prover.prove_masked_with_attempt.match_".isPrefixOf n.toString then
        logInfo m!"MATCHER {n}"
        evalTactic (← `(tactic| try delta $(mkIdent n)))
  simp only [Aeneas.Std.uncurry, erase_59 base F ops, erase_60 base F ops,
    erase_61 base F ops, erase_83 base F ops, erase_108 base F ops,
    erase_116 base F ops, erase_134 base F ops, erase_257 base F ops hw h12,
    erase_325 base F ops, erase_336 base F ops, erase_341 base F ops,
    erase_342 base F ops, erase_421 base F ops, erase_422 base F ops]
  simp only [PDict_FormatterTypeMaps.compilation]
  all_goals rfl

#print axioms erase_423
end R1Z.PDict_Static222
