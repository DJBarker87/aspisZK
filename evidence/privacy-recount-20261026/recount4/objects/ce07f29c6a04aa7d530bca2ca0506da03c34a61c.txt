import R1Z.BuilderNullifierExtracted
import R1Z.BuilderRecordsArray

/-! Total preimage and exact owned-callback semantics. The callback may be
partial and stateful; neither totality nor a cryptographic property is assumed. -/
set_option autoImplicit false
namespace R1Z.BuilderNullifierReference
open Aeneas Aeneas.Std Result AspisBuilderNullifierReference R0Z.WriterRefine
open spend.nullifier_reference
abbrev Digest := Array U32 8#usize

def preimage (key salt : Digest) : Array U32 16#usize :=
  Array.make 16#usize [key.val[0]!, key.val[1]!, key.val[2]!, key.val[3]!, key.val[4]!, key.val[5]!, key.val[6]!, key.val[7]!, salt.val[0]!, salt.val[1]!, salt.val[2]!, salt.val[3]!, salt.val[4]!, salt.val[5]!, salt.val[6]!, salt.val[7]!]

theorem preimage_owned_eq (key salt : Digest) :
    preimage_owned key salt = ok (preimage key salt) := by
  rw [preimage_owned]
  rw [index_ok key 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok key 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok key 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok key 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok key 4#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok key 5#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok key 6#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok key 7#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok salt 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok salt 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok salt 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok salt 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok salt 4#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok salt 5#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok salt 6#usize (by decide)]
  simp only [bind_tc_ok]
  rw [index_ok salt 7#usize (by decide)]
  simp only [bind_tc_ok]
  rfl

theorem key_at (key salt : Digest) (i : Nat) (hi : i < 8) :
    (preimage key salt).val[i]! = key.val[i]! := by
  interval_cases i <;> rfl

theorem salt_at (key salt : Digest) (i : Nat) (hi : i < 8) :
    (preimage key salt).val[8+i]! = salt.val[i]! := by
  interval_cases i <;> rfl

theorem owned_callback {H : Type}
    (f : core.ops.function.FnMut H (U32 × Array U32 16#usize) Digest)
    (key salt : Digest) (state : H) :
    derive_nullifier_owned_with f key salt state = (do
      let (d,_) ← f.call_mut state (spend.DOMAIN_NULLIFIER,preimage key salt)
      ok d) := by
  rw [derive_nullifier_owned_with,preimage_owned_eq]
  rfl

theorem owned_success {H : Type}
    (f : core.ops.function.FnMut H (U32 × Array U32 16#usize) Digest)
    (key salt d : Digest) (state after : H)
    (h : f.call_mut state (spend.DOMAIN_NULLIFIER,preimage key salt) = ok (d,after)) :
    derive_nullifier_owned_with f key salt state = ok d := by
  rw [owned_callback,h]
  rfl

#print axioms preimage_owned_eq
#print axioms key_at
#print axioms salt_at
#print axioms owned_callback
#print axioms owned_success
end R1Z.BuilderNullifierReference
