import NMT_345CloneSemantics
set_option autoImplicit false
namespace NMT_345CloneSemantics
open RSL

def getData (a : OwnedAccount) : RS Bytes :=
 match a.bytes with
 | .ok b => RS.pure b
 | .error e => RS.bind (cloneError e) RS.throw

theorem data_on_snapshot (a : OwnedAccount)
 (safe : ∀ e,a.bytes = .error e → SnapshotError e) :
 getData a = RS.ofExcept a.data := by
 unfold getData OwnedAccount.data
 cases hb : a.bytes with
 | ok bytes => rfl
 | error e =>
  change RS.bind (cloneError e) RS.throw = RS.ofExcept (.error e)
  rw [snapshot_clone e (safe e hb),RS.bind_pure]
  rfl

theorem data_string_abort (a : OwnedAccount) (msg : String)
 (deferred : a.bytes = .error (.borshIoError msg)) (nonempty : msg.isEmpty = false) (env : Env) :
 getData a env ⟨.abort,[]⟩ := by
 unfold getData
 rw [deferred]
 unfold RS.bind
 apply Or.inr
 apply Or.inl
 exact ⟨[],string_clone_abort msg nonempty env,rfl⟩

/-- The old pure getter reference cannot admit the same stop. -/
theorem pure_data_no_abort (a : OwnedAccount) (env : Env) :
 ¬ RS.ofExcept a.data env ⟨.abort,[]⟩ := by
 simp [RS.ofExcept,Spec.pure]
#print axioms data_on_snapshot
#print axioms data_string_abort
#print axioms pure_data_no_abort
end NMT_345CloneSemantics
