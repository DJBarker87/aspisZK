import NLV_PairElim
import Lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmissionSource
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
/-- Focused structural normalization: only named suffix definitions and the
pair eliminator are expanded. The earlier broad congruence shape is retired. -/
theorem source (cfg : Configuration) (i : Input) :
 NLV_Emitted.suffix_guard cfg i = GExp_FirstCode.code cfg.base cfg.boundaries cfg.std
 i.hashv i.digest i.publicValue i.publicBytes i.proof i.k := by
 simp only [NLV_Emitted.suffix_guard,NLV_Emitted.suffix_parse,NLV_Emitted.suffix_scan,NLV_Emitted.suffix_markParsed,NLV_Emitted.suffix_zero,NLV_Emitted.suffix_prepare,NLV_Emitted.suffix_accumulator,NLV_Emitted.suffix_markPrepare,NLV_Emitted.suffix_foldedSlice,NLV_Emitted.suffix_foldedCopy,NLV_Emitted.suffix_foldedUnwrap,NLV_Emitted.suffix_batch0,NLV_Emitted.suffix_markMerkle,NLV_Emitted.suffix_geometry,NLV_Emitted.suffix_pending,NLV_Emitted.suffix_query,NLV_Emitted.suffix_finishPending,NLV_Emitted.suffix_checkpoint,NLV_Emitted.suffix_markCheckpoint,NLV_Emitted.suffix_returned,
  GExp_FirstCode.code,NLV_Emitted.emittedTry,NLJ_Tx1.ops,NLV_PairElim.elim,Bind.bind,Pure.pure,NLV_Algebra.assoc,CheckpointBytes5Effect.bind]
 run_tac
   let target ← Lean.Elab.Tactic.getMainTarget
   let lhs := target.appFn!.appArg!
   let rhs := target.appArg!
   let rec diff : Nat → Lean.Expr → Lean.Expr → Option (Lean.Expr × Lean.Expr)
    | 0,a,b => some (a,b)
    | n+1,a,b =>
      if a==b then none else
      match a,b with
      | .app f x,.app g y => (diff n f g).orElse (fun _ => diff n x y)
      | .lam _ t x _,.lam _ u y _ => (diff n t u).orElse (fun _ => diff n x y)
      | .forallE _ t x _,.forallE _ u y _ => (diff n t u).orElse (fun _ => diff n x y)
      | .letE _ t v x _,.letE _ u w y _ => (diff n t u).orElse (fun _ => (diff n v w).orElse (fun _=>diff n x y))
      | .mdata _ x,y => diff n x y
      | x,.mdata _ y => diff n x y
      | .const c _,.const d _ => if c==d then none else some (a,b)
      | .proj c i x,.proj d j y => if c==d && i==j then diff n x y else some (a,b)
      | _,_ => some (a,b)
   match diff 500 lhs rhs with
   | some (a,b) => Lean.logInfo m!"NLV_FIRST_AST_DIFF: {a} versus {b}"
   | none => Lean.logInfo "NLV_FIRST_AST_DIFF: alpha-equivalent structure"
 try rfl
#print axioms source
end AspisR1.NLV_EmissionSource
end
