import NNG_Tree094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareTree094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Context094 NMT_CallTree NNG_Tree094
-- Correct full typed arguments at the prepare call; emitted body is unchanged.
def NNG_call_5 (NMT_call_5 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice
    Std.U8) → H → (Option (verifier.Phase → Result Unit)) → (Array
    aspis_core.field.wide_exact.WideExact 29#usize) → Result
    ((core.result.Result verifier.Prepared verifier.Error) × (Array
    aspis_core.field.wide_exact.WideExact 29#usize))) {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (a0 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (a1 : (Slice Std.U8)) (a2 : H) (a3 : (Option (verifier.Phase → Result Unit))) (a4 : (Array aspis_core.field.wide_exact.WideExact 29#usize)) : Code ((core.result.Result verifier.Prepared verifier.Error) × (Array aspis_core.field.wide_exact.WideExact 29#usize)) :=
 invoke "TX1:087/prepare" (aspis_coredigestDigest32Inst,a0,a1,a2,a3,a4) (NMT_call_5 aspis_coredigestDigest32Inst a0 a1 a2 a3 a4)
def f_r2 {H : Type} (c : Calls) (parent : Parent H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let (r2, g1) ←
    (NNG_call_5 c.c5) aspis_coredigestDigest32Inst public1 proof
      hash obs g
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
  match cf2 with
  | core.ops.control_flow.ControlFlow.Continue val =>
    f_r3 c parent g1 val
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_we {H : Type} (c : Calls) (parent : Parent H) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let we ← (NNG_call_0 c.c0)
  let g := Array.repeat 29#usize we
  f_r2 c parent g

def f_markParsed {H : Type} (c : Calls) (parent : Parent H) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  (NNG_call_11 c.c11) obs verifier.Phase.Parsed
  f_we c parent

def f_r1 {H : Type} (c : Calls) (parent : Parent H) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r1 ← (NNG_call_2 c.c2) proof
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    f_markParsed c parent
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error)
      residual

def f_r {H : Type} (c : Calls) (parent : Parent H) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  let r ← (NNG_call_1 c.c1) proof
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    f_r1 c parent
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

def f_guard {H : Type} (c : Calls) (parent : Parent H) : Code Output := do
  let aspis_coredigestDigest32Inst:=parent.digest
  let public1:=parent.publicValue
  let public_bytes:=parent.publicBytes
  let proof:=parent.proof
  let k:=parent.k
  let hash:=parent.hash
  let obs:=parent.observer
  if k != compact.SPLIT
  then ok (core.result.Result.Err verifier.Error.Parse)
  else
    f_r c parent

end AspisR1.NNG_PrepareTree094
