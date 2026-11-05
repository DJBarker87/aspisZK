import NHC_Hints.Funs
set_option autoImplicit false
namespace NHP_AccountPrelude
abbrev Error := AdapterRw.solana_program_error.ProgramError
structure Metadata where
  ownerMatches : Bool
  executable : Bool
  writableMatches : Bool
  signer : Bool
  deriving DecidableEq

def program (m : Metadata) : Option Error :=
  if !m.ownerMatches then some .IncorrectProgramId
  else if m.executable || !m.writableMatches then some .InvalidAccountData
  else none

def beforeImage (m : Metadata) (borrowSucceeds : Bool) : Option Error :=
  match program m with
  | some e => some e
  | none => if m.signer then some .InvalidAccountData
            else if !borrowSucceeds then some .AccountBorrowFailed else none

theorem owner_first (m : Metadata) (h : m.ownerMatches = false) :
    program m = some .IncorrectProgramId := by simp [program,h]
#print axioms owner_first

theorem metadata_second (m : Metadata) (ho : m.ownerMatches = true)
    (hbad : m.executable = true ∨ m.writableMatches = false) :
    program m = some .InvalidAccountData := by
  rcases hbad with he | hw
  · simp [program,ho,he]
  · simp [program,ho,hw]
#print axioms metadata_second

theorem program_continue (m : Metadata) : program m = none ↔
    m.ownerMatches = true ∧ m.executable = false ∧ m.writableMatches = true := by
  cases m with
  | mk o e w s => cases o <;> cases e <;> cases w <;> simp [program]
#print axioms program_continue

theorem signer_before_borrow (m : Metadata) (hp : program m = none)
    (hs : m.signer = true) (borrow : Bool) :
    beforeImage m borrow = some .InvalidAccountData := by simp [beforeImage,hp,hs]
#print axioms signer_before_borrow

theorem failed_borrow_before_image (m : Metadata) (hp : program m = none)
    (hs : m.signer = false) :
    beforeImage m false = some .AccountBorrowFailed := by simp [beforeImage,hp,hs]
#print axioms failed_borrow_before_image

theorem image_domain (m : Metadata) (borrow : Bool) :
    beforeImage m borrow = none ↔
      m.ownerMatches = true ∧ m.executable = false ∧ m.writableMatches = true ∧
      m.signer = false ∧ borrow = true := by
  cases m with
  | mk o e w s =>
    cases o <;> cases e <;> cases w <;> cases s <;> cases borrow <;>
      simp [beforeImage,program]
#print axioms image_domain

theorem rejection_borrow_independent (m : Metadata) (e : Error)
    (h : program m = some e) (a b : Bool) : beforeImage m a = beforeImage m b := by
  simp [beforeImage,h]
#print axioms rejection_borrow_independent
end NHP_AccountPrelude
