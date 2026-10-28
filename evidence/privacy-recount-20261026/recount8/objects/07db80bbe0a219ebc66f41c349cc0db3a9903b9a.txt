import R1Z.ProverCommitOwnerZero42
import R1Z.ProverCommitPublicNonce40
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOwnerBytes42
open Aeneas Aeneas.Std Result AspisR1PublicNonce41 ProverCommitOwnerZero42
open R0Z.FsStatement (OracleAnswer)
attribute [local instance] Classical.propDecidable

def byte (b : U8) : UInt8 := ⟨b.bv⟩
def block (bytes : Bytes) : OracleAnswer := fun j => byte (getByte bytes j)

theorem byte_zero (b : U8) : byte b = 0 ↔ b = 0#u8 := by
  constructor
  · intro h
    apply UScalar.eq_of_val_eq
    exact congrArg UInt8.toNat h
  · intro h; subst h; rfl

theorem block_zero (bytes : Bytes) : block bytes = 0 ↔ ∀ j, getByte bytes j = 0#u8 := by
  constructor
  · intro h j; apply (byte_zero _).mp; exact congrFun h j
  · intro h; funext j; exact (byte_zero _).mpr (h j)

theorem zero_block (bytes : Bytes) : owner.zero bytes 0#u8 = ok (decide (block bytes = 0)) := by
  rw [zero_spec]
  simp only [block_zero]

def raw (r : owner.Raw) : ProverCommitPublicNonce40.Raw :=
  Fin.cases (block r.field) (fun _ => block r.leaf)

theorem raw_good (r : owner.Raw) :
    (∀ j, raw r j ≠ 0) ↔ block r.field ≠ 0 ∧ block r.leaf ≠ 0 := by
  constructor
  · intro h; exact ⟨h 0,h 1⟩
  · rintro ⟨hf,hl⟩ j
    fin_cases j <;> assumption

#print axioms byte_zero
#print axioms block_zero
#print axioms zero_block
#print axioms raw_good
end R1Z.ProverCommitOwnerBytes42
