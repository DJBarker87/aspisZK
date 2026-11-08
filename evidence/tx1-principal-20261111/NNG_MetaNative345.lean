-- Canonical RSL retarget of NMT_R2_CheckpointMeta; source/proof structure retained.
import NNG_EquationNative345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_MetaNative345
open Aeneas Aeneas.Std NMT_345 RSL AspisR1.NNG_EquationNative345
attribute [local instance] Classical.propDecidable

def bad (a : Account) (program : Key) (writable : Bool) : Bool :=
 decide (a.owner ≠ program) || a.is_signer || a.executable || a.is_writable != writable

theorem bad_canonical (a : Account) (program : Key) (writable : Bool) :
 (decide ((account a).owner ≠ key program) || (account a).is_signer ||
  (account a).executable || (account a).is_writable != writable) = bad a program writable := by
 have he : key a.owner = key program ↔ a.owner = program :=
  ⟨fun h => key_injective h,fun h => congrArg key h⟩
 unfold bad account
 by_cases h : a.owner = program
 · have hk : key a.owner = key program := he.mpr h
   simp only [h,hk,ne_eq,not_true_eq_false,decide_false]
 · have hk : key a.owner ≠ key program := fun e => h (he.mp e)
   simp only [h,hk,ne_eq,not_false_eq_true,decide_true]

theorem native_normalized (keep : Bool) (a : Account) (program : Key) (writable : Bool) :
 native keep a program writable =
 (if bad a program writable then .ok (.Err .InvalidAccountData)
 else do
  let length ← AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len
   (AspisR1.NNG_LengthNative345.ops keep) (toAccount a)
  finish length) := by
 rw [equation]
 unfold bad
 by_cases ho : a.owner ≠ program
 · simp [ho]
 · simp only [ho,decide_false,Bool.false_or,if_false]
   cases a.is_signer <;> cases a.executable <;> cases a.is_writable <;> cases writable <;> rfl
#print axioms bad_canonical
#print axioms native_normalized
end AspisR1.NNG_MetaNative345
end
