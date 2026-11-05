import NGL_ReadonlyModel
import NIM_NGL_MetaReferenceModel
set_option autoImplicit false
noncomputable section
namespace NHJ_ReadonlyPacket
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev Key := NGL_ReadonlyModel.Key
abbrev Account := NGL_ReadonlyModel.Account
abbrev PE := NGL_ReadonlyModel.PE
/-- Bool-encoded complete reachable ProgramResult carrier. True is Ok unit. -/
def reply (b : Bool) : core.result.Result Unit PE :=
  if b then .Ok () else .Err .InvalidAccountData

def accepted (owner expected : Key) (s w e : Bool) : Bool :=
  !((!(decide (owner = expected))) || s || w || e)

structure Arguments where
  owner : Key
  expected : Key
  signer : Bool
  writable : Bool
  executable : Bool

def arguments (a : Account) (expected : Key) : Arguments :=
  ⟨a.owner, expected, a.is_signer, a.is_writable, a.executable⟩
/-- G of the caller's one local log record, with arbitrary complete child reply. -/
def G (_args : Arguments) (loggedReply : Bool) : core.result.Result Unit PE :=
  reply loggedReply
/-- Concrete child substitution; no caller output or successful-run premise. -/
theorem metadata (ops : AdapterRw.Ops) (owner expected : Key) (s w e : Bool) :
    AdapterRw.r1_pool_adapter.readonly_meta_ok (NGL_ReadonlyModel.install ops)
      owner expected s w e = ok (reply (accepted owner expected s w e)) := by
  rw [NGL_ReadonlyModel.metadata_result]
  unfold reply accepted
  cases (!(decide (owner = expected))) || s || w || e <;> rfl

theorem readonly (ops : AdapterRw.Ops) (a : Account) (expected : Key) :
    AdapterRw.r1_pool_adapter.owned.require_readonly_account
      (NGL_ReadonlyModel.install ops) a expected =
    ok (G (arguments a expected)
      (accepted a.owner expected a.is_signer a.is_writable a.executable)) := by
  change AdapterRw.r1_pool_adapter.readonly_meta_ok (NGL_ReadonlyModel.install ops)
    a.owner expected a.is_signer a.is_writable a.executable = _
  exact metadata ops a.owner expected a.is_signer a.is_writable a.executable

#print axioms metadata
#print axioms readonly
end NHJ_ReadonlyPacket
