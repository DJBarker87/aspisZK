import NMX_R3_PrimaryDigestRun
import NMX_R3_DigestWords
set_option autoImplicit false
namespace NMX_R3_DigestPositive
open Aeneas Aeneas.Std Result NMX_R3_DigestWords

def Canonical (b : Slice U8) (s : Nat) : Prop :=
 ∀ k, k < 8 → (limb b s k).val < 2147483647

/-- The complete success run follows from every symbolic limb check. -/
theorem value (b : Slice U8) (s : Usize) (cap : b.val.length ≤ 768)
 (fit : s.val + 32 ≤ b.val.length) (canonical : Canonical b s.val) :
 NCV_Reference.digest b s = ok (.Ok (target b s.val)) := by
 apply NMX_R3_PrimaryDigestRun.value b s (target b s.val)
  (fun k => NDB_PrimaryWords.window b (s.val+4*k) 4#usize) cap fit
 · intro k hk
   exact (NMX_R3_PrimaryWindow.bytes b (s.val+4*k) 4#usize (by change s.val+4*k+4 ≤ b.val.length; omega)).symm
 · intro k hk
   exact (coordinate b s.val k hk).symm
 · exact canonical
#print axioms value
end NMX_R3_DigestPositive
