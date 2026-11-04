import NFQ_ZeroReference
set_option autoImplicit false
noncomputable section
namespace NFQ_ZeroSource
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

def result (b : Bool) : core.result.Result Unit solana_program_error.ProgramError :=
 if b then .Ok () else .Err .AccountAlreadyInitialized

theorem source (bytes : Slice U8) (bound : bytes.val.length≤4096) :
    r1_pool_adapter.owned.require_zero bytes =
      (do let b ← NFQ_ScanReference.zero_ref bytes;ok (result b)) := by
  unfold r1_pool_adapter.owned.require_zero
  rw [← NFQ_ZeroReference.loop_reference bytes bound bytes.val.length 0#usize (by change 0+bytes.val.length=bytes.val.length;omega)]
  simp only [NFQ_ScanReference.zero_ref, bind_assoc]
  congr 1
  funext b
  cases b <;> rfl
#print axioms source
end NFQ_ZeroSource
