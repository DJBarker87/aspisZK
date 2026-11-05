import NHJ_DataPacket
import NGL_LengthCarrier
set_option autoImplicit false
noncomputable section
namespace NHJ_LengthPacket
open Aeneas Aeneas.Std Result
abbrev Account := NGL_CloneDomain.Account
abbrev PE := NGL_CloneDomain.PE
/-- The exact core Result::clone arm schedule; only the Err payload is an oracle. -/
def G (a : Account) (loggedErrorReply : Bool) :=
  match a.length with
  | .Ok n => core.result.Result.Ok n
  | .Err _ => core.result.Result.Err (NHJ_DataPacket.errorReply loggedErrorReply)
def childReply (a : Account) : Bool :=
  match a.length with
  | .Ok _ => false
  | .Err e => NHJ_DataPacket.encodeError e

theorem substitute (ops : AdapterRw.Ops) (a : Account)
    (domain : ∀ e, a.length = .Err e → NGL_CloneDomain.SnapshotError e) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len
      (NGL_CloneDomain.install ops) a = ok (G a (childReply a)) := by
  rw [NGL_CloneDomain.length_result]
  cases h : a.length with
  | Ok n => simp only [h,G]
  | Err e =>
    simp only [h,G,childReply]
    rw [NHJ_DataPacket.exact_error e (domain e h)]

/-- The actual snapshot storage constructors imply the stronger sole-borrow error law. -/
theorem storage_domain (a : Account) (domain : NGL_StorageCases.Domain a) :
    ∀ e, a.length = .Err e → e = AdapterRw.solana_program_error.ProgramError.AccountBorrowFailed := by
  intro e h
  rcases domain.1 with ⟨hl,_⟩ | ⟨n,hl,_⟩ | ⟨n,v,hl,_,_,_⟩
  · exact core.result.Result.Err.inj (h.symm.trans hl)
  · rw [hl] at h
    cases h
  · rw [hl] at h
    cases h
#print axioms substitute
#print axioms storage_domain
end NHJ_LengthPacket
