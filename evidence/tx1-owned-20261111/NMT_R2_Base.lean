import NMT_RSL_Base
set_option autoImplicit false
namespace RSL

def Spec.allocIf (b : Bool) : Spec Unit := if b then alloc else Spec.pure ()

def ProgramError.cloneAllocates : ProgramError → Bool
  | .borshIoError msg => !msg.isEmpty
  | _ => false

/-- `match r { Ok(x) => Ok(x), Err(e) => Err(e.clone()) }` followed by `?`:
the Err arm passes the clone's allocation site (ruling (bl)(3): fresh String or
abort with the prefix so far) before returning the cloned error. -/
def RS.ofCloned {α : Type} (x : Except ProgramError α) : RS α :=
  match x with
  | .ok a => RS.pure a
  | .error e => if e.cloneAllocates then RS.bind (RS.lift Spec.alloc) (fun _ => RS.throw e)
                else RS.throw e

theorem RS.ofCloned_ok {α : Type} (a : α) : (RS.ofCloned (.ok a) : RS α) = RS.pure a := rfl

theorem RS.ofCloned_error {α : Type} (e : ProgramError) (h : e.cloneAllocates = false) :
    (RS.ofCloned (.error e) : RS α) = RS.throw e := by
  simp [RS.ofCloned, h]

/-- On a value whose error (if any) carries no heap payload, the clone is the
plain Result. -/
theorem RS.ofCloned_eq_ofExcept {α : Type} (x : Except ProgramError α)
    (h : ∀ e, x = .error e → e.cloneAllocates = false) : RS.ofCloned x = RS.ofExcept x := by
  cases x with
  | ok a => rfl
  | error e => exact RS.ofCloned_error e (h e rfl)

theorem Spec.bind_two {α β : Type} (m : Spec α) (k : α → Spec β) (env : Env) (x : α)
    (hm : ∀ o, m env o ↔ o = ⟨.ret x, []⟩ ∨ o = ⟨.abort, []⟩) (o : Obs β) :
    Spec.bind m k env o ↔ k x env o ∨ o = ⟨.abort, []⟩ := by
  constructor
  · intro h
    rcases h with ⟨a, e1, o2, h1, h2, ho⟩ | ⟨e1, h1, ho⟩ | ⟨e1, h1, ho⟩
    · rcases (hm _).mp h1 with h | h
      · simp only [Obs.mk.injEq, Exit.ret.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        subst ho; left; cases o2; simpa using h2
      · simp at h
    · rcases (hm _).mp h1 with h | h
      · simp at h
      · simp only [Obs.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        exact Or.inr ho
    · rcases (hm _).mp h1 with h | h <;> simp at h
  · rintro (h | rfl)
    · exact Or.inl ⟨x, [], o, (hm _).mpr (Or.inl rfl), h, by cases o; rfl⟩
    · exact Or.inr (Or.inl ⟨[], (hm _).mpr (Or.inr rfl), rfl⟩)

theorem RS.lift_alloc_iff (env : Env) (o : Obs (Except ProgramError Unit)) :
    RS.lift Spec.alloc env o ↔ o = ⟨.ret (.ok ()), []⟩ ∨ o = ⟨.abort, []⟩ := by
  unfold RS.lift Spec.map
  rw [Spec.bind_two _ _ env () (fun _ => Iff.rfl)]
  rfl

/-- `alloc; k`: exactly the silent allocation abort, or `k`. -/
theorem RS.alloc_seq_iff {β : Type} (k : RS β) (env : Env) (o : Obs (Except ProgramError β)) :
    RS.seq (RS.lift Spec.alloc) k env o ↔ k env o ∨ o = ⟨.abort, []⟩ := by
  unfold RS.seq RS.bind
  rw [Spec.bind_two _ _ env (.ok ()) (RS.lift_alloc_iff env)]


end RSL
namespace NMT_R2
open RSL
def data (a : OwnedAccount) : RS Bytes := RS.ofCloned a.bytes
def data_len (a : OwnedAccount) : RS Nat := RS.ofCloned a.length
def verifierCheckpoint (a : OwnedAccount) (program : B32) (writable : Bool) : RS Unit :=
 if decide (a.owner ≠ program) || a.is_signer || a.executable || a.is_writable != writable then
  RS.throw .invalidAccountData
 else RS.bind (data_len a) fun n => RS.check (n != CHECKPOINT_BYTES) .invalidAccountData
end NMT_R2

#print axioms RSL.RS.ofCloned_ok

#print axioms RSL.RS.ofCloned_error

#print axioms RSL.RS.ofCloned_eq_ofExcept

#print axioms RSL.Spec.bind_two

#print axioms RSL.RS.lift_alloc_iff

#print axioms RSL.RS.alloc_seq_iff
