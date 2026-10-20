import AspisR1DotPushLocal.Funs
import EbyKDotPushActualFoldV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1DotPushLocal.Proof
open AspisR1EbyKDotPushActualFoldV2 AspisR1.EbyKDotPushCanonicalFoldBridgeV1

def updateWord (old raw : U64) : U64 :=
  core.num.U64.wrapping_add old (actualWrappingFold raw)

def emittedWord (old raw : U64) : Result U64 := do
  let mask ← lift (core.convert.num.FromU64U32.from canonical.P)
  let low ← lift (raw &&& mask)
  let high ← raw >>> 31#i32
  let folded ← lift (core.num.U64.wrapping_add low high)
  lift (core.num.U64.wrapping_add old folded)

theorem emittedWord_total (old raw : U64) :
    emittedWord old raw = .ok (updateWord old raw) := by
  simp only [emittedWord,canonical.P,lift,bind_tc_ok]
  rfl

theorem updateWord_value (old raw : U64) (hold : old.val < 2 ^ 46) :
    (updateWord old raw).val = old.val + AspisR1EbyKDotPushNatStep.foldedRaw raw.val ∧
    (updateWord old raw).val % AspisR1EbyKDotPushNatStep.modulus =
      (old.val + raw.val) % AspisR1EbyKDotPushNatStep.modulus := by
  obtain ⟨hv,_,hm⟩ := actual_wrapping_fold_coordinate_step hold (raw:=raw)
  exact ⟨hv,by rw [show (updateWord old raw).val=old.val+AspisR1EbyKDotPushNatStep.foldedRaw raw.val from hv];exact hm⟩

#print axioms emittedWord_total
#print axioms updateWord_value
end AspisR1DotPushLocal.Proof
