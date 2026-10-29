import PV_DIAG3_Drop
/-! Noncustom io::Error destruction. Error::repr is repr_bitpacked on the
64-bit deployed target. Its Drop decodes the tag; only Custom creates an
owned Box. All other decoded fields are scalar or static shared references.
This tag-level theorem is restricted to valid native Repr values. Validity,
provenance and kind_from_prim for arbitrary incoming words are not proved here.
The OS constructor's tag is proved without reducing a 64-bit computation. -/
set_option autoImplicit false
namespace PV_DIAG4
open PV_DIAG3
variable {S : Type}
-- This is the destructor's branch on a decoded VALID native representation.
-- Custom's complete Box/trait object/allocator execution is retained.
inductive ValidErrorRepr (C : Type) where
 | os (codeBits : Fin (2^32))
 | simple (kind : Nat)
 | message (staticAddress : Nat)
 | custom (owned : C)
 deriving Repr
def errorTag {C : Type} : ValidErrorRepr C → Nat
 | .os _ => 2 | .simple _ => 3 | .message _ => 0 | .custom _ => 1
def errorReprDrop {C : Type} (customDrop : C → Op S Unit) : ValidErrorRepr C → Op S Unit
 | .custom c => customDrop c
 | .os _ => PV_DIAG3.pure ()
 | .simple _ => PV_DIAG3.pure ()
 | .message _ => PV_DIAG3.pure ()
def osWord (codeBits : Fin (2^32)) : Nat := codeBits.val * 2^32 + 2
theorem os_constructor_tag (code : Fin (2^32)) : osWord code % 4 = 2 := by
 simp [osWord,Nat.add_mod,Nat.mul_mod]
#print axioms os_constructor_tag
theorem os_drop_exact {C : Type} (drop : C → Op S Unit) (code : Fin (2^32)) :
 errorReprDrop drop (.os code) = PV_DIAG3.pure () := rfl
#print axioms os_drop_exact
theorem simple_drop_exact {C : Type} (drop : C → Op S Unit) (kind : Nat) :
 errorReprDrop drop (.simple kind) = PV_DIAG3.pure () := rfl
#print axioms simple_drop_exact
theorem message_drop_exact {C : Type} (drop : C → Op S Unit) (address : Nat) :
 errorReprDrop drop (.message address) = PV_DIAG3.pure () := rfl
#print axioms message_drop_exact
theorem custom_drop_retained {C : Type} (drop : C → Op S Unit) (c : C) :
 errorReprDrop drop (.custom c) = drop c := rfl
#print axioms custom_drop_retained
theorem noncustom_drop_exact {C : Type} (drop : C → Op S Unit) (e : ValidErrorRepr C)
 (h : errorTag e ≠ 1) : errorReprDrop drop e = PV_DIAG3.pure () := by
 cases e <;> simp_all [errorTag,errorReprDrop]
#print axioms noncustom_drop_exact
theorem os_error_unwind_silent {C : Type} (drop : C → Op S Unit) (code : Fin (2^32))
 (dp : Panic → Panic → Op S Unit) (p : Panic) (s : S) :
 unwind p (errorReprDrop drop (.os code)) dp s = ⟨[],s,.panic p⟩ := by
 simp [os_drop_exact,unwind,PV_DIAG3.pure,prepend]
#print axioms os_error_unwind_silent
end PV_DIAG4
