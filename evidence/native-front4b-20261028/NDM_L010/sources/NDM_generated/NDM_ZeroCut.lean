import NDM_ZeroSuffix
set_option autoImplicit false
namespace NDM_ZeroCut
open Aeneas Aeneas.Std Result
abbrev Answer := ControlFlow Usize (Option (core.result.Result Unit
 AdapterRw.solana_program_error.ProgramError))

def decode (next : Usize) (tag : U8) : Answer :=
 if tag=0#u8 then .done none
 else if tag=1#u8 then .done (some (.Err .AccountAlreadyInitialized))
 else .cont next

theorem terminal (base : Slice U8) (i next : Usize) (bound : base.val.length≤i.val) :
 (do let tag ← NDM_Reference.zero_tail_ref (NDG_ZeroStep.byte base i.val) true
     ok (decode next tag)) =
 AdapterRw.r1_pool_adapter.owned.require_zero_loop.body base i := by
 rw [NDG_ZeroStep.terminal base i bound]
 rfl

theorem step (base : Slice U8) (i : Usize) (cap : base.val.length≤65536)
 (bound : i.val<base.val.length) :
 ∃ next : Usize, next.val=i.val+1 ∧
 (do let tag ← NDM_Reference.zero_tail_ref (NDG_ZeroStep.byte base i.val) false
     ok (decode next tag)) =
 AdapterRw.r1_pool_adapter.owned.require_zero_loop.body base i := by
 obtain ⟨next,value,body⟩ := NDG_ZeroStep.step base i cap bound
 refine ⟨next,value,?_⟩
 rw [body]
 by_cases zero : NDG_ZeroStep.byte base i.val=0#u8
 · simp [NDM_Reference.zero_tail_ref,decode,zero]
 · simp [NDM_Reference.zero_tail_ref,decode,zero]

theorem suffix_step (base tail : Slice U8) (i : Usize)
 (same : tail.val=base.val.drop i.val) (cap : base.val.length≤65536)
 (bound : i.val<base.val.length) :
 ∃ next : Usize, next.val=i.val+1 ∧
 (do let tag ← NDM_Reference.zero_tail_ref (NDG_ZeroStep.byte tail 0) false
     ok (decode next tag)) =
 AdapterRw.r1_pool_adapter.owned.require_zero_loop.body base i := by
 have head := NDM_ZeroSuffix.byte_drop base tail i.val 0 same
 simp only [Nat.add_zero] at head
 rw [head]
 exact step base i cap bound

#print axioms terminal
#print axioms step
#print axioms suffix_step
end NDM_ZeroCut
