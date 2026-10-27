import Hist_InitialZero
import S2W_D189Wrappers
import S2X_RuntimeRetention
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_Store
open Aeneas Aeneas.Std Result S2W_D189Entry
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

structure Cell where
  owner : S2W_ExtractionBoundary.Program
  data : Slice U8
abbrev Store := Nat → Cell

def put (store : Store) (key : Nat) (value : Cell) : Store :=
  fun at => if at = key then value else store at

def byteLedger (store : Store) : Nat → Bytes := fun key => MultiproofConeCanonical.bytesOf (store key).data.val

def Initialized (s : Slice U8) : Prop :=
  0 < s.val.length ∧ Slice.index_usize s 0#usize = ok (82#u8)

/-- Runtime ownership and account loading are the external Solana trust boundary.
The first branch records the actual EXTRACTED owned call, including its own zero
and authority checks. TX2's wrapper has no account write (second_accepted).
A successful readonly call and a rollback have the same empty DATA effect. -/
inductive Step (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program) :
    Store → S2X.AccountEvent → Store → Prop where
  | rollback (store : Store) : Step ops program store .rollback store
  | foreign (store : Store) (key : Nat) (caller : S2W_ExtractionBoundary.Program) (value : Cell)
      (different : caller ≠ program) (authorized : (store key).owner = caller) :
      Step ops program store (.committedWrite key (MultiproofConeCanonical.bytesOf value.data.val))
        (put store key value)
  | first (store : Store) (key : Nat) (e : Entry) (data : Slice U8) (saved : alloc.vec.Vec U8)
      (loaded : e.buffers (e.handles 2).1 = (store key).data)
      (authorized : (store key).owner = program)
      (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e.first data = ok (.Ok saved)) :
      Step ops program store (.committedWrite key (MultiproofConeCanonical.bytesOf saved.val))
        (put store key ⟨(store key).owner,saved.deref⟩)
  | second (store : Store) (e : Entry) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
      (accepted : AdapterRw.r1_pool_adapter.owned.stage2_owned ops program
        (e.second S2W_D189Wrappers.secondSizes) data slot = ok (.Ok ())) :
      Step ops program store .rollback store

inductive Trace (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program) :
    Store → List S2X.AccountEvent → Store → Prop where
  | nil (store : Store) : Trace ops program store [] store
  | cons {before middle after : Store} {event : S2X.AccountEvent} {events : List S2X.AccountEvent}
      (head : Step ops program before event middle)
      (tail : Trace ops program middle events after) :
      Trace ops program before (event :: events) after

theorem put_here (store : Store) (key : Nat) (value : Cell) : put store key value key = value := by
  simp only [put,if_pos rfl]

theorem put_other (store : Store) (key at : Nat) (value : Cell) (different : at ≠ key) :
    put store key value at = store at := by
  simp only [put,if_neg different]

#print axioms put_here
#print axioms put_other
end AspisR1.Hist_Store
end
