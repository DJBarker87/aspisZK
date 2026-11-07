import NMT_first.Funs
import NMT_CallTree
set_option autoImplicit false
noncomputable section
namespace NMT_first
open Aeneas Aeneas.Std Result
/-- Std Result::map_err, with the actual callback invoked only on Err. -/
def NMT_std_map_err {T E F O : Type} (inst : core.ops.function.FnOnce O E F)
 (r : core.result.Result T E) (o : O) : Result (core.result.Result T F) :=
 match r with
 | .Ok value => .ok (.Ok value)
 | .Err error => do let mapped ← inst.call_once o error; .ok (.Err mapped)
/-- All native outer Result arms are retained. A stopped child never invokes
its continuation, so a stopped prefix acquires no suffix callback. -/
theorem NMT_bind_complete {A B : Type} (r : Result A) (k : A → Result B) :
 (r >>= k) = match r with
 | .ok a => k a
 | .fail e => .fail e
 | .div => .div := by
 cases r <;> rfl
#print axioms NMT_bind_complete
/-- Fresh emitted328, std mapper interpreted by its complete library law.
This is an emitted-body fold, not a native row root or a child endpoint premise. -/
theorem NMT_emitted_fold (NMT_call_1 : ∀ {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H),
aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice
    Std.U8) → (Slice Std.U8) → Std.Usize → H → (Option
    (aspis_r1_cost_probe.verifier.Phase → Result Unit)) → Result
    (core.result.Result (alloc.vec.Vec Std.U8)
    aspis_r1_cost_probe.verifier.Error)) (NMT_call_4 : solana_hash.Hash → Result (Array Std.U8 32#usize)) (NMT_call_5 : (Slice (Slice Std.U8)) → Result solana_hash.Hash) (NMT_call_6 : aspis_r1_cost_probe.verifier.Error → Result
    solana_program_error.ProgramError) 
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize) :
  first_decoded NMT_std_map_err NMT_call_1 NMT_call_4 NMT_call_5 NMT_call_6 public1 public_bytes proof k =
  (do
    let r ← NMT_call_1 (SolanaDigest.Insts.Aspis_coreDigestDigest32 NMT_call_4 NMT_call_5) public1 public_bytes proof k () none
    match r with
    | .Ok bytes => .ok (.Ok bytes)
    | .Err e => do let mapped ← NMT_call_6 e; .ok (.Err mapped))
 := by
 unfold first_decoded observer NMT_std_map_err
 simp only [bind_tc_ok, BuiltinFnOnce]
 cases h : NMT_call_1 (SolanaDigest.Insts.Aspis_coreDigestDigest32 NMT_call_4 NMT_call_5) public1 public_bytes proof k () none with
 | fail e => simp [h,Aeneas.Std.bind]
 | div => simp [h,Aeneas.Std.bind]
 | ok r => cases r <;> simp [h,Aeneas.Std.bind]
#print axioms NMT_emitted_fold
end NMT_first
