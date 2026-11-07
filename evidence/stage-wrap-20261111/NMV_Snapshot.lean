import NLF_SnapshotFold
set_option autoImplicit false
namespace NMV_Snapshot
open NLF_SdkModel NLF_ParentModel

inductive Error where
  | borrow | invalidData
  deriving DecidableEq
structure Owned where
  key : List UInt8
  owner : List UInt8
  signer : Bool
  writable : Bool
  executable : Bool
  length : Except Error Nat
  bytes : Except Error (List UInt8)
  deriving DecidableEq

/-- Frozen lines 30–39: the clone is value identity under std; guard events
and restoration come from the NLF bracket, including the conflict arm. -/
def fields (r : Except NLF_SdkModel.ProgramError Payload) (l₁ l₂ : Nat) :
    Except Error Nat × Except Error (List UInt8) :=
  match r with
  | .error _ => (.error .borrow,.error .borrow)
  | .ok p => (.ok p.bytes.length,
      if p.bytes.length = l₁ ∨ p.bytes.length = l₂ then .ok p.bytes else .error .invalidData)

def owned (a : Account) (r : Except NLF_SdkModel.ProgramError Payload) (l₁ l₂ : Nat) : Owned :=
  let v := fields r l₁ l₂
  ⟨a.key,a.owner,a.signer,a.writable,a.executable,v.1,v.2⟩

/-- Complete snapshot transcription; no successful-borrow premise. -/
def run (p : Parent) (a l₁ l₂ : Nat) : Parent × Owned :=
  let r := NLF_SnapshotEvents.step p a
  (r.1,owned (p.state.accounts a) r.2 l₁ l₂)

theorem frame (p : Parent) (a l₁ l₂ : Nat) :
    (run p a l₁ l₂).1.state = p.state :=
  NLF_SnapshotEvents.step_frame p a

theorem exact (p : Parent) (a l₁ l₂ : Nat) :
    run p a l₁ l₂ =
      (⟨p.state,p.next+1,p.events ++ NLF_SnapshotEvents.events p.state a p.next⟩,
       owned (p.state.accounts a) (NLF_Bracket.snapshot p.state a p.next).2 l₁ l₂) := by
  dsimp only [run, NLF_SnapshotEvents.step]
  rw [NLF_Bracket.snapshot_frame]

theorem rejected_length (a : Account) (p : Payload) (l₁ l₂ : Nat)
    (h₁ : p.bytes.length ≠ l₁) (h₂ : p.bytes.length ≠ l₂) :
    (owned a (.ok p) l₁ l₂).length = .ok p.bytes.length ∧
    (owned a (.ok p) l₁ l₂).bytes = .error .invalidData := by
  simp [owned,fields,h₁,h₂]

theorem admitted (a : Account) (p : Payload) (l₁ l₂ : Nat)
    (h : p.bytes.length = l₁ ∨ p.bytes.length = l₂) :
    (owned a (.ok p) l₁ l₂).bytes = .ok p.bytes := by simp [owned,fields,h]

theorem borrow_error (a : Account) (l₁ l₂ : Nat) :
    (owned a (.error .accountBorrowFailed) l₁ l₂).length = .error .borrow ∧
    (owned a (.error .accountBorrowFailed) l₁ l₂).bytes = .error .borrow := by
  exact ⟨rfl,rfl⟩

#print axioms frame
#print axioms exact
#print axioms rejected_length
#print axioms admitted
#print axioms borrow_error
end NMV_Snapshot
