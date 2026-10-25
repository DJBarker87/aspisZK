import Hist_Persistence
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_Nonvacuity
open Aeneas Aeneas.Std Result Hist_Store
abbrev Key := S2W_ExtractionBoundary.Program

def key (byte : U8) : Key := Array.make 32#usize (List.replicate 32 byte)
def checkpoint : Slice U8 := ⟨82#u8 :: List.replicate 1767 (0#u8),by simp; scalar_tac⟩
def original : Store := fun n => ⟨if n = 0 then key 0#u8 else key 1#u8,checkpoint⟩
def changed : Cell := ⟨key 1#u8,⟨[7#u8],by simp; scalar_tac⟩⟩

theorem different : key 1#u8 ≠ key 0#u8 := by
  intro eq
  have same := congrArg (fun k : Key => k.val[0]?) eq
  change some (1#u8) = some (0#u8) at same
  exact (by decide : (1#u8) ≠ 0#u8) (Option.some.inj same)

theorem initialized : Initialized checkpoint := by
  constructor
  · simp [checkpoint]
  · simp [checkpoint,Slice.index_usize]

/-- The source-indexed history allows a genuine authorized foreign write and
a subsequent rollback. It is not the synthetic empty-history witness. This
is local runtime-model non-vacuity, not a jointly accepted crypto fixture. -/
theorem trace_exists (ops : AdapterRw.Ops) :
    ∃ (before after : Store) (events : List S2X.AccountEvent),
      events ≠ [] ∧ Trace ops (key 0#u8) before events after ∧
      (before 0).owner = key 0#u8 ∧ Initialized (before 0).data ∧
      byteLedger after 0 = byteLedger before 0 := by
  let events : List S2X.AccountEvent := [.committedWrite 1 (MultiproofConeCanonical.bytesOf changed.data.val),.rollback]
  have first : Step ops (key 0#u8) original events.head! (put original 1 changed) :=
    Step.foreign original 1 (key 1#u8) changed different (by simp [original])
  have trace : Trace ops (key 0#u8) original events (put original 1 changed) :=
    Trace.cons first (Trace.cons (Step.rollback _) (Trace.nil _))
  refine ⟨original,put original 1 changed,events,by intro h; cases h,trace,?_,?_,?_⟩
  · simp [original]
  · exact initialized
  · exact Hist_Persistence.retained ops (key 0#u8) original (put original 1 changed) 0 events trace
      (by simp [original]) initialized

#print axioms different
#print axioms initialized
#print axioms trace_exists
end AspisR1.Hist_Nonvacuity
end
