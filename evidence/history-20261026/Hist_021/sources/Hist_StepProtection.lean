import Hist_Store
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_StepProtection
open Aeneas Aeneas.Std Result S2W_D189Entry Hist_Store

theorem writer_different (store : Store) (key target : Nat)
    (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (e : Entry) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (loaded : e.buffers (e.handles 2).1 = (store target).data)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e.first data = ok (.Ok saved))
    (initialized : Initialized (store key).data) : key ≠ target := by
  intro same
  subst target
  have nonempty : 0 < (e.buffers (e.handles 2).1).val.length := by rw [loaded]; exact initialized.1
  have read : Slice.index_usize (e.buffers (e.handles 2).1) 0#usize = ok (82#u8) := by
    rw [loaded]; exact initialized.2
  exact Hist_InitialZero.no_reinitialize e ops program data saved (82#u8) nonempty read
    (by decide) accepted

/-- The program's own zero check proves exclusion of its writes. The external
branch uses only runtime account-ownership authorization. -/
theorem step_frame (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (before after : Store) (key : Nat) (event : S2X.AccountEvent)
    (step : Step ops program before event after)
    (owner : (before key).owner = program)
    (initialized : Initialized (before key).data) :
    S2X.Preserves key event ∧ after key = before key := by
  cases step with
  | rollback => exact ⟨True.intro,rfl⟩
  | second => exact ⟨True.intro,rfl⟩
  | foreign store target caller value different authorized =>
    have distinct : key ≠ target := by
      intro same
      subst target
      exact different (authorized.symm.trans owner)
    exact ⟨distinct,put_other store target key value distinct⟩
  | first store target e data saved loaded authorized accepted =>
    have distinct := writer_different store key target ops program e data saved loaded accepted initialized
    exact ⟨distinct,put_other store target key _ distinct⟩

#print axioms writer_different
#print axioms step_frame
end AspisR1.Hist_StepProtection
end
