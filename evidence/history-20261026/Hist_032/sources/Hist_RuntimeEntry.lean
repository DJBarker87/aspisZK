import Hist_Store
import Hist_Authority
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_RuntimeEntry
open Aeneas Aeneas.Std Result S2W_D189Entry Hist_Store

/-- Per-invocation runtime metadata/layout. Data and ownership are loaded from
ledger state; privileges remain specific to this invocation. Same cell labels
mean the same runtime account, as in existing RuntimeEntrypointAdmission. -/
structure Layout where
  handles : Nat → Nat × Nat
  records : Nat → Record
  base : Nat → Nat
  provenance : Nat → Nat

def load (store : Store) (layout : Layout) : Entry where
  handles := layout.handles
  records := fun c => {layout.records c with owned :=
    {(layout.records c).owned with owner := (store c).owner}}
  buffers := fun c => (store c).data
  base := layout.base
  provenance := layout.provenance

def commit (store : Store) (key : Nat) (saved : alloc.vec.Vec U8) : Store :=
  put store key ⟨(store key).owner,saved.deref⟩

theorem loaded_data (store : Store) (layout : Layout) (slot : Nat) :
    (load store layout).buffers ((load store layout).handles slot).1 =
      (store (layout.handles slot).1).data := rfl

theorem commit_data (store : Store) (key : Nat) (saved : alloc.vec.Vec U8) :
    (commit store key saved key).data.val = saved.val := by
  simp [commit,put,alloc.vec.Vec.deref]

theorem commit_owner (store : Store) (key : Nat) (saved : alloc.vec.Vec U8) :
    (commit store key saved key).owner = (store key).owner := by
  simp [commit,put]

/-- The ledger account's ownership follows from the program's actual guard,
with concrete pure library equality, rather than a runtime authorization field. -/
theorem accepted_owner (base : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (store : Store) (layout : Layout) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (Hist_Authority.install base)
      program (load store layout).first data = ok (.Ok saved)) :
    (store (layout.handles 2).1).owner = program := by
  obtain ⟨account,index,owner⟩ := Hist_Authority.accepted_owner base program (load store layout).first data saved accepted
  have same := Result.ok.inj (index.symm.trans (first_index (load store layout)).2.2)
  subst account
  exact owner

#print axioms loaded_data
#print axioms commit_data
#print axioms commit_owner
#print axioms accepted_owner
end AspisR1.Hist_RuntimeEntry
end
