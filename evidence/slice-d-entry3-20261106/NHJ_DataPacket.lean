import NGL_CloneDomain
import NGL_HelperFrames
import NGL_StorageCases
set_option autoImplicit false
noncomputable section
namespace NHJ_DataPacket
open Aeneas Aeneas.Std Result
abbrev Account := NGL_CloneDomain.Account
abbrev PE := NGL_CloneDomain.PE

def errorReply (borrow : Bool) : PE :=
  if borrow then .AccountBorrowFailed else .InvalidAccountData

def encodeError : PE → Bool
  | .AccountBorrowFailed => true
  | _ => false

theorem exact_error (e : PE) (domain : NGL_CloneDomain.SnapshotError e) :
    errorReply (encodeError e) = e := by
  rcases domain with h|h <;> subst e <;> rfl

/-- Local-record G: successful borrowed window unchanged, complete clone reply on Err. -/
def G (a : Account) (loggedErrorReply : Bool) :=
  match a.bytes with
  | .Ok v => core.result.Result.Ok v.deref
  | .Err _ => core.result.Result.Err (errorReply loggedErrorReply)

def childReply (a : Account) : Bool :=
  match a.bytes with
  | .Ok _ => false
  | .Err e => encodeError e

theorem substitute (ops : AdapterRw.Ops) (a : Account)
    (domain : ∀ e, a.bytes = .Err e → NGL_CloneDomain.SnapshotError e) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
      (NGL_CloneDomain.install ops) a = ok (G a (childReply a)) := by
  rw [NGL_CloneDomain.data_result]
  cases h : a.bytes with
  | Ok v => simp only [h,G,childReply]
  | Err e =>
    simp only [h,G,childReply]
    rw [exact_error e (domain e h)]

/-- Every successful concrete snapshot model establishes the clone domain;
    the copy and borrow laws are supplied by that snapshot packet, never by data. -/
theorem storage_domain (a : Account) (domain : NGL_StorageCases.Domain a) :
    ∀ e, a.bytes = .Err e → NGL_CloneDomain.SnapshotError e := by
  intro e h
  rcases domain.1 with ⟨_,hb⟩ | ⟨n,_,hb⟩ | ⟨n,v,_,hb,_,_⟩
  · exact Or.inl (core.result.Result.Err.inj (h.symm.trans hb))
  · exact Or.inr (core.result.Result.Err.inj (h.symm.trans hb))
  · rw [hb] at h
    cases h

#print axioms exact_error
#print axioms substitute
#print axioms storage_domain
end NHJ_DataPacket
