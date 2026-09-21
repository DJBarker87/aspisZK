import AspisV8R17.SourceMaskLoop
import Mathlib.Data.List.OfFn

/-! The inner zero_boundary power loop in r17_structured_g.rs. Symbolic
induction handles every width; no concrete cube or large recurrence reduces.
Rust array bounds and QM31 machine arithmetic remain separate refinements. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [Field F]

def zeroBoundaryLoop (x : F) (out power : F) (cs : List F) : F × F :=
  cs.foldl (fun acc c => (acc.1 + c * (acc.2 - x), acc.2 * x)) (out,power)

theorem zeroBoundaryLoop_closed (n k : ℕ) (cs : Fin n → F) (x out : F) :
    zeroBoundaryLoop x out (x^k) (List.ofFn cs) =
      (out + ∑ i, cs i * (x^(k+i.val) - x), x^(k+n)) := by
  induction n generalizing k out with
  | zero => simp [zeroBoundaryLoop]
  | succ n ih =>
    simp only [zeroBoundaryLoop, List.ofFn_succ, List.foldl_cons]
    change zeroBoundaryLoop x (out + cs 0 * (x^k-x)) (x^k*x)
      (List.ofFn (fun i => cs i.succ)) = _
    rw [← pow_succ, ih]
    simp [Fin.sum_univ_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_assoc]

def sourceZeroBoundary {n : ℕ} (a : F) (cs : Fin n → F) (x : F) : F :=
  (zeroBoundaryLoop x (a * (1 - (x+x))) (x^2) (List.ofFn cs)).1

theorem sourceZeroBoundary_eq_roundEval {n : ℕ} (a : F) (cs : Fin n → F) (x : F) :
    sourceZeroBoundary a cs x = roundEval a cs x := by
  unfold sourceZeroBoundary
  rw [zeroBoundaryLoop_closed]
  simp only [Prod.fst, roundEval, Nat.add_comm 2]
  congr 1
  ring

theorem sourceZeroBoundary_add {n : ℕ} (a b : F) (cs ds : Fin n → F) (x : F) :
    sourceZeroBoundary (a+b) (fun i => cs i + ds i) x =
      sourceZeroBoundary a cs x + sourceZeroBoundary b ds x := by
  simp only [sourceZeroBoundary_eq_roundEval, roundEval, add_mul, Finset.sum_add_distrib]
  ring

def literalMaskContributions {width : ℕ} : (r : ℕ) →
    RoundCoins (F × (Fin width → F)) r → RoundCoins F r → List F
  | 0, _, _ => []
  | r+1, coins, z => sourceZeroBoundary coins.1.1 coins.1.2 z.1 ::
      literalMaskContributions r coins.2 z.2

theorem literalMaskContributions_eq {width : ℕ} (r : ℕ)
    (coins : RoundCoins (F × (Fin width → F)) r) (z : RoundCoins F r) :
    literalMaskContributions r coins z = maskContributions r coins z := by
  induction r with
  | zero => rfl
  | succ r ih => simp [literalMaskContributions, maskContributions,
      sourceZeroBoundary_eq_roundEval, ih]

theorem literalMaskLoop_eq_structuredMask [NeZero (2 : F)] {width : ℕ}
    (r : ℕ) (carry : F) (coins : RoundCoins (F × (Fin width → F)) r)
    (z : RoundCoins F r) :
    sourceMaskLoop (1/2) carry (literalMaskContributions r coins z) =
      structuredMask r carry coins z := by
  rw [literalMaskContributions_eq]
  exact sourceMaskLoop_eq_structuredMask r carry coins z

/-- Literal staged terminal replacement: remove the ordinary G factor and
add the serialized structured G claim. base contains all non-G terms. -/
def replacedGTerminal (base factor g : F) : F := (base + factor*g) - g*factor + g

theorem replacedGTerminal_eq (base factor g : F) :
    replacedGTerminal base factor g = base + g := by
  unfold replacedGTerminal
  ring

theorem old_g_cancels_from_context_offset (left right factor g : F) :
    replacedGTerminal left factor g - replacedGTerminal right factor g = left-right := by
  simp only [replacedGTerminal_eq]
  ring

theorem corrected_g_terminal (left right factor g delta : F) (h : delta = left-right) :
    replacedGTerminal right factor (g+delta) = replacedGTerminal left factor g := by
  simp only [replacedGTerminal_eq, h]
  ring

#print axioms zeroBoundaryLoop_closed
#print axioms sourceZeroBoundary_eq_roundEval
#print axioms sourceZeroBoundary_add
#print axioms literalMaskContributions_eq
#print axioms literalMaskLoop_eq_structuredMask
#print axioms replacedGTerminal_eq
#print axioms old_g_cancels_from_context_offset
#print axioms corrected_g_terminal
end AspisV8R17
