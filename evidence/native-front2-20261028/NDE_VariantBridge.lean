import NDE_Reference3.Funs
import NDE_RawBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_VariantBridge
abbrev Q := NDE_Reference3.Q
abbrev V := FIq_Native.pool_v1.pair_forest_semantic_terminal.CompiledVariant

def toNative (q : Q) : FIq_Native.field.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def isWithdrawal : V → Bool
  | .PrivateTransfer => false | .Withdrawal => true
def mapFour (v : Q × Q × Q × Q) :
    FIq_Native.field.QM31 × FIq_Native.field.QM31 × FIq_Native.field.QM31 × FIq_Native.field.QM31 :=
  (toNative v.1,toNative v.2.1,toNative v.2.2.1,toNative v.2.2.2)

theorem word_reference (a b : U32) :
    NDE_Reference3.add_word_ref a b = FIq_Native.field.M31.add a b := by
  unfold NDE_Reference3.add_word_ref FIq_Native.field.M31.add
  simp only [FIq_Native.field.P]
  cases h : a + b with
  | fail e => rfl
  | div => rfl
  | ok s =>
    simp only [h, bind_tc_ok]
    split
    · cases s - 2147483647#u32 <;> rfl
    · rfl

theorem add_reference (a b : Q) :
    NDE_LiftBridge.mapResult toNative (NDE_Reference3.add_ref a b) =
    FIq_Native.field.QM31.add (toNative a) (toNative b) := by
  simp only [NDE_Reference3.add_ref, FIq_Native.field.QM31.add,
    FIq_Native.field.CM31.add, NDE_RawBridge.map_bind,
    word_reference, toNative, bind_assoc_eq, bind_tc_ok]
  rfl

#print axioms word_reference
#print axioms add_reference
end NDE_VariantBridge
