import NMS_R2Success
set_option autoImplicit false
namespace NMS_R2N_CloneReference
open RSL
/-- Proposed exact std-side interpretation for the frozen derived Clone:
ordinary variants return unchanged; a nonempty String clone has one private
allocation site. Under (bl)(3) its failure is a prefix-only transaction abort.
No native row credit or new trust is asserted by defining this reference. -/
def clone (e : ProgramError) : Spec ProgramError :=
 match e with
 | .borshIoError text =>
   if text.isEmpty then Spec.pure e
   else Spec.bind Spec.alloc (fun _ => Spec.pure e)
 | _ => Spec.pure e

def data (account : OwnedAccount) : RS Bytes :=
 match account.bytes with
 | .ok bytes => RS.pure bytes
 | .error error => Spec.bind (clone error) (fun reply => RS.throw reply)

/-- The two error variants produced by the actual snapshot caller. -/
def SnapshotErrors (account : OwnedAccount) : Prop :=
 ∀ error, account.bytes = .error error → error = .accountBorrowFailed ∨ error = .invalidAccountData

theorem success (account : OwnedAccount) (env : Env) (bytes : Bytes) (events : List Event)
 (run : data account env ⟨.ret (.ok bytes),events⟩) : account.bytes = .ok bytes := by
 unfold data at run
 cases stored : account.bytes with
 | ok original =>
   simp only [stored] at run
   have same := Except.ok.inj (NMS_R2Success.pure_return _ _ env events run)
   exact congrArg Except.ok same.symm
 | error e =>
   simp only [stored] at run
   obtain ⟨_,_,_,_,last,_⟩ := NMS_R2Success.bind_return _ _ _ _ _ run
   have impossible := NMS_R2Success.pure_return _ _ _ _ last
   cases impossible

theorem snapshot_data (account : OwnedAccount) (safe : SnapshotErrors account) :
 data account = RS.ofExcept account.bytes := by
 unfold data RS.ofExcept
 cases stored : account.bytes with
 | ok bytes => rfl
 | error e =>
   rcases safe e stored with same | same
   · subst e
     exact Spec.bind_pure _ _
   · subst e
     exact Spec.bind_pure _ _

#print axioms success
#print axioms snapshot_data
end NMS_R2N_CloneReference
