import R1Z.PV_RunJoin_BankAggregate18
import R1Z.PV_Src_PortFullRoundCopy
set_option autoImplicit false
namespace R1Z.PV_RunJoin_IndexedSbox19
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep

theorem initial (n : Nat) (iter : core.ops.range.Range Usize)
    (hcount : iter.start.val+n=16) (hend : iter.end.val=16) (s c : State) :
    poseidon2.apply_round_by_index_loop0 iter s c =
      poseidon2.permute_optimized_with_trace_loop0_loop0 iter s c := by
  induction n generalizing iter s with
  | zero =>
    rw [poseidon2.apply_round_by_index_loop0,
      poseidon2.permute_optimized_with_trace_loop0_loop0,
      BuilderBankRange.next_none iter (by omega)]
    rfl
  | succ n ih =>
    obtain ⟨after,hn,ha,he⟩ := BuilderBankRange.next_some iter (by omega)
    rw [poseidon2.apply_round_by_index_loop0,
      poseidon2.permute_optimized_with_trace_loop0_loop0,hn]
    simp only [bind_tc_ok]
    simp only [ih after (by rw [ha];omega) (by rw [he];exact hend)]
#print axioms initial
end R1Z.PV_RunJoin_IndexedSbox19
