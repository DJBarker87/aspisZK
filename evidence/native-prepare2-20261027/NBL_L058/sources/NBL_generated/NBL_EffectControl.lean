import NBL_CodeMonad
import S1PreparedCompleteHashErasureV1
import NBL_PrepareControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_EffectControl
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedScratchReachability
open NBL_PrepareControl
abbrev Code := PreparedHashCode.Code

/-- Source-order opening prefix; its output is the sole carrier into the
query/rho/powers/claim continuation. This factors the EXISTING typed effect-code tree. -/
def opening (B : PreparedSourceEffects.Effects Code) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) : Code (Opening H) := do
  let state ← r1_wire.SemanticTranscript.impl.state D sem.transcript
  let start ← B.newTranscript D hash state v.variant
  let (gamma,t1) ← B.scalar D start 27#u8 v.y1 true
  let bytes ← B.toBytes v.inactive
  let payload ← lift (Array.to_slice bytes)
  let (kappa,t2) ← B.scalar D t1 28#u8 payload false
  let (alpha0,t3) ← B.scalar D t2 29#u8 v.round0 false
  let folds ← transport.Variant.folds v.variant
  if folds=2#usize then
    let capacity ← 32#usize+224#usize
    let root ← core.option.Option.unwrap v.folded_root
    let payload ← lift (Array.to_slice root)
    let b1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 capacity) payload
    let b2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 b1 v.round1
    let (alpha1,t4) ← B.scalar D t3 30#u8 (alloc.vec.Vec.deref b2) false
    pure ⟨gamma,kappa,Array.make 2#usize [alpha0,alpha1],t4,31#u8⟩
  else
    let zero ← OriginalPreparedNative.zero
    pure ⟨gamma,kappa,Array.make 2#usize [alpha0,zero],t3,30#u8⟩

/-- Full continuation, including both Rust Result errors and scratch writes. -/
def continuation (B : PreparedSourceEffects.Effects Code) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (old : Scratch) (o : Opening H) : Code Out := do
  let (r,t1) ← B.queries D o.transcript o.row v.final_message
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue queries =>
    let row ← o.row+1#u8
    let payload ← lift (Array.to_slice (Std.Array.empty U8))
    let (rho,t2) ← B.rho D t1 row payload
    let g ← B.powers 29#usize o.gamma
    let r ← B.claim D sem v.y1 v.inactive g o.kappa
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | .Continue claim => pure (.Ok (output sem v o.gamma o.kappa o.alpha rho queries claim t2),g)
    | .Break residual =>
      let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        verifier.Prepared (core.convert.FromSame verifier.Error) residual
      pure (r,g)
  | .Break residual =>
    let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      verifier.Prepared (core.convert.FromSame verifier.Error) residual
    pure (r,old)

def program (B : PreparedSourceEffects.Effects Code) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (old : Scratch) : Code Out := do
  let o ← opening B D sem v hash
  continuation B D sem v old o

/-- Full typed effect-code equality, universally quantified over effect dictionaries and inputs.
No successful child observations or native/model equality is a hypothesis. -/
theorem source (B : PreparedSourceEffects.Effects Code) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (old : Scratch) :
    PreparedSourceEffects.prepare B D sem v hash old=program B D sem v hash old := by
  unfold PreparedSourceEffects.prepare program opening
  simp only [NBL_CodeMonad.associative]
  apply NBL_CodeMonad.bind_same; intro state
  apply NBL_CodeMonad.bind_same; intro start
  apply NBL_CodeMonad.bind_same; rintro ⟨gamma,t1⟩
  simp only [NBL_CodeMonad.associative,Aeneas.Std.uncurry]
  apply NBL_CodeMonad.bind_same; intro bytes
  apply NBL_CodeMonad.bind_same; intro payload
  apply NBL_CodeMonad.bind_same; rintro ⟨kappa,t2⟩
  simp only [NBL_CodeMonad.associative,Aeneas.Std.uncurry]
  apply NBL_CodeMonad.bind_same; rintro ⟨alpha0,t3⟩
  simp only [NBL_CodeMonad.associative,Aeneas.Std.uncurry]
  apply NBL_CodeMonad.bind_same; intro folds
  split <;> simp only [NBL_CodeMonad.associative,NBL_CodeMonad.pure_bind,continuation,output,Aeneas.Std.uncurry]
  all_goals repeat' (apply NBL_CodeMonad.bind_same; intro x; try dsimp! only; try simp only [NBL_CodeMonad.associative,NBL_CodeMonad.pure_bind,Aeneas.Std.uncurry])
  all_goals rfl

#print axioms source
end AspisR1.NBL_EffectControl
end
