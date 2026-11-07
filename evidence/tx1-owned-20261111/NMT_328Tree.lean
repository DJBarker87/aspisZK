import NMT_first.Funs
import NMT_CallTree
set_option autoImplicit false
noncomputable section
namespace NMT_first
open Aeneas Aeneas.Std Result
open AspisR1.NMT_CallTree
def NMT_328_NMT_call_0 (NMT_call_0 : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F), (core.result.Result T E) → O → Result (core.result.Result T F)) {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F) (a0 : (core.result.Result T E)) (a1 : O) : Code (core.result.Result T F) :=
 invoke "core.result.Result.map_err" (opsfunctionFnOnceOTupleEFInst,a0,a1) (NMT_call_0 opsfunctionFnOnceOTupleEFInst a0 a1)
def NMT_328_NMT_call_1 (NMT_call_1 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H), aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice
    Std.U8) → (Slice Std.U8) → Std.Usize → H → (Option
    (aspis_r1_cost_probe.verifier.Phase → Result Unit)) → Result
    (core.result.Result (alloc.vec.Vec Std.U8)
    aspis_r1_cost_probe.verifier.Error)) {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (a0 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (a1 : (Slice Std.U8)) (a2 : (Slice Std.U8)) (a3 : Std.Usize) (a4 : H) (a5 : (Option (aspis_r1_cost_probe.verifier.Phase → Result Unit))) : Code (core.result.Result (alloc.vec.Vec Std.U8) aspis_r1_cost_probe.verifier.Error) :=
 invoke "aspis_r1_cost_probe.verifier.candidate.tx1" (aspis_coredigestDigest32Inst,a0,a1,a2,a3,a4,a5) (NMT_call_1 aspis_coredigestDigest32Inst a0 a1 a2 a3 a4 a5)
def NMT_328_NMT_call_4 (NMT_call_4 : solana_hash.Hash → Result (Array Std.U8 32#usize))  (a0 : solana_hash.Hash) : Code (Array Std.U8 32#usize) :=
 invoke "solana_hash.Hash.to_bytes" a0 (NMT_call_4 a0)
def NMT_328_NMT_call_5 (NMT_call_5 : (Slice (Slice Std.U8)) → Result solana_hash.Hash)  (a0 : (Slice (Slice Std.U8))) : Code solana_hash.Hash :=
 invoke "solana_sha256_hasher.hashv" a0 (NMT_call_5 a0)
def NMT_328_NMT_call_6 (NMT_call_6 : aspis_r1_cost_probe.verifier.Error → Result
    solana_program_error.ProgramError)  (a0 : aspis_r1_cost_probe.verifier.Error) : Code solana_program_error.ProgramError :=
 invoke "error" a0 (NMT_call_6 a0)
def NMT_328_tree (NMT_call_0 : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F),
(core.result.Result T E) → O → Result (core.result.Result T F)) (NMT_call_1 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice
    Std.U8) → (Slice Std.U8) → Std.Usize → H → (Option
    (aspis_r1_cost_probe.verifier.Phase → Result Unit)) → Result
    (core.result.Result (alloc.vec.Vec Std.U8)
    aspis_r1_cost_probe.verifier.Error)) (NMT_call_4 : solana_hash.Hash → Result (Array Std.U8 32#usize)) (NMT_call_5 : (Slice (Slice Std.U8)) → Result solana_hash.Hash) (NMT_call_6 : aspis_r1_cost_probe.verifier.Error → Result
    solana_program_error.ProgramError) 
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize) :
  Code (core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError)
  := do
  let o ← observer
  let r ←
    (NMT_328_NMT_call_1 NMT_call_1)
      (SolanaDigest.Insts.Aspis_coreDigestDigest32 NMT_call_4 NMT_call_5) public1 public_bytes proof k
      () o
  (NMT_328_NMT_call_0 NMT_call_0) (BuiltinFnOnce aspis_r1_cost_probe.verifier.Error
    solana_program_error.ProgramError) r (NMT_call_6)

theorem NMT_328_erase (NMT_call_0 : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F),
(core.result.Result T E) → O → Result (core.result.Result T F)) (NMT_call_1 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice
    Std.U8) → (Slice Std.U8) → Std.Usize → H → (Option
    (aspis_r1_cost_probe.verifier.Phase → Result Unit)) → Result
    (core.result.Result (alloc.vec.Vec Std.U8)
    aspis_r1_cost_probe.verifier.Error)) (NMT_call_4 : solana_hash.Hash → Result (Array Std.U8 32#usize)) (NMT_call_5 : (Slice (Slice Std.U8)) → Result solana_hash.Hash) (NMT_call_6 : aspis_r1_cost_probe.verifier.Error → Result
    solana_program_error.ProgramError) 
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize) :
 erase (NMT_328_tree NMT_call_0 NMT_call_1 NMT_call_4 NMT_call_5 NMT_call_6 public1 public_bytes proof k) = first_decoded NMT_call_0 NMT_call_1 NMT_call_4 NMT_call_5 NMT_call_6 public1 public_bytes proof k := by
 unfold NMT_328_tree first_decoded
 simp only [Bind.bind, Pure.pure, MonadLift.monadLift, AspisR1.NMT_CallTree.bind,erase,invoke, erase_bind,erase_lift,erase_pure,erase_invoke,result_right,result_assoc,NMT_328_NMT_call_0,NMT_328_NMT_call_1,NMT_328_NMT_call_4,NMT_328_NMT_call_5,NMT_328_NMT_call_6]
 repeat' first
 | rfl
 | (split <;> simp only [Bind.bind, Pure.pure, MonadLift.monadLift, AspisR1.NMT_CallTree.bind,erase,invoke, erase_bind,erase_lift,erase_pure,erase_invoke,result_right,result_assoc,NMT_328_NMT_call_0,NMT_328_NMT_call_1,NMT_328_NMT_call_4,NMT_328_NMT_call_5,NMT_328_NMT_call_6])
 | (congr 1 <;> first | rfl | (funext x; simp only [Bind.bind, Pure.pure, MonadLift.monadLift, AspisR1.NMT_CallTree.bind,erase,invoke, erase_bind,erase_lift,erase_pure,erase_invoke,result_right,result_assoc,NMT_328_NMT_call_0,NMT_328_NMT_call_1,NMT_328_NMT_call_4,NMT_328_NMT_call_5,NMT_328_NMT_call_6]))
#print axioms NMT_328_erase
end NMT_first
