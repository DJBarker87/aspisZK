import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_EntryReads
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers

theorem data (ops : AdapterRw.Ops) (entry : Entry) (index first second : Nat)
    (length : (entry.buffers (entry.handles index).1).val.length=first ∨
      (entry.buffers (entry.handles index).1).val.length=second) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (entry.snapshot index first second)=
      ok (.Ok (entry.buffers (entry.handles index).1)) := by
  unfold AdapterRw.r1_pool_adapter.owned.OwnedAccount.data Entry.snapshot
  dsimp only
  rw [if_pos length]
  rfl
#print axioms data

theorem count (entry : Entry) : Slice.len (entry.second secondSizes)=7#usize := by
  apply UScalar.eq_of_val_eq
  change (List.ofFn (fun i : Fin 7=>entry.snapshot i.val (secondSizes i.val).1 (secondSizes i.val).2)).length=7
  exact List.length_ofFn
#print axioms count
end AspisR1.JGx_EntryReads
end
