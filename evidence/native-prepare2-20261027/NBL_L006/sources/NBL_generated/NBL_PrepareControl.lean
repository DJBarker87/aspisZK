import NBA_TraceReplay
import NBA_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_PrepareControl
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedScratchReachability
abbrev PE := aspis_core.field.WideExact
abbrev Scratch := Array PE 29#usize
abbrev Out := core.result.Result verifier.Prepared verifier.Error × Scratch

structure Opening (H : Type) where
  gamma : PE
  kappa : PE
  alpha : Array PE 2#usize
  transcript : transcript.Transcript H
  row : U8

/-- Source-order opening prefix; its output is the sole carrier into the
query/rho/powers/claim continuation. This is a cohort factor, not a native law. -/
def opening (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) : Result (Opening H) := do
  let state ← r1_wire.SemanticTranscript.impl.state D sem.transcript
  let start ← transcript.Transcript.new D hash state v.variant
  let (gamma,t1) ← PreparedModel.scalar B.sampling D start 27#u8 v.y1 true
  let bytes ← B.sampling.toBytes v.inactive
  let payload ← lift (Array.to_slice bytes)
  let (kappa,t2) ← PreparedModel.scalar B.sampling D t1 28#u8 payload false
  let (alpha0,t3) ← PreparedModel.scalar B.sampling D t2 29#u8 v.round0 false
  let folds ← transport.Variant.folds v.variant
  if folds=2#usize then
    let capacity ← 32#usize+224#usize
    let root ← core.option.Option.unwrap v.folded_root
    let payload ← lift (Array.to_slice root)
    let b1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 capacity) payload
    let b2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 b1 v.round1
    let (alpha1,t4) ← PreparedModel.scalar B.sampling D t3 30#u8 (alloc.vec.Vec.deref b2) false
    ok ⟨gamma,kappa,Array.make 2#usize [alpha0,alpha1],t4,31#u8⟩
  else
    ok ⟨gamma,kappa,Array.make 2#usize [alpha0,aspis_core.field.WideExact.ZERO],t3,30#u8⟩

/-- Full continuation, including both Rust Result errors and scratch writes. -/
def continuation (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (old : Scratch) (o : Opening H) : Result Out := do
  let (r,t1) ← B.sampling.queries D o.transcript o.row v.final_message
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue queries =>
    let row ← o.row+1#u8
    let payload ← lift (Array.to_slice (Std.Array.empty U8))
    let (rho,t2) ← PreparedModel.scalar_k B.sampling D t1 row payload
    let g ← B.powers 29#usize o.gamma
    let r ← B.claim D sem v.y1 v.inactive g o.kappa
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | .Continue claim => ok (.Ok (output sem v o.gamma o.kappa o.alpha rho queries claim t2),g)
    | .Break residual =>
      let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        verifier.Prepared (core.convert.FromSame verifier.Error) residual
      ok (r,g)
  | .Break residual =>
    let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      verifier.Prepared (core.convert.FromSame verifier.Error) residual
    ok (r,old)

def run (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (old : Scratch) : Result Out := do
  let o ← opening B D sem v hash
  continuation B D sem v old o

/-- Full Result equality, universally quantified over boundaries and inputs.
No successful child observations or native/model equality is a hypothesis. -/
theorem source (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (old : Scratch) :
    PreparedScratchModel.prepare B D sem v hash old=run B D sem v hash old := by
  unfold PreparedScratchModel.prepare run opening
  simp only [bind_assoc_eq,Aeneas.Std.uncurry]
  repeat' (apply NBA_QueryJoin.bind_same; intro x; simp only [bind_assoc_eq,Aeneas.Std.uncurry])
  split <;> simp only [bind_assoc_eq,bind_tc_ok,continuation,output,Aeneas.Std.uncurry]
  all_goals repeat' (apply NBA_QueryJoin.bind_same; intro x; simp only [bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry])
  all_goals rfl

#print axioms source
end AspisR1.NBL_PrepareControl
end
