import R1Z.ProverCommitQuotientLaw
import R1Z.CommitReadsR1
import R1J.SamplerLawSpend

/-! The exact accepted M31 word carrier, with its two raw-word preimages.
No finite stream or tape is enumerated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitWordCarrier
open R1Z.CommitReadsR1
attribute [local instance] Classical.propDecidable
local notation "p" => AspisCircleGroupOrder.P
variable {K : Type} [Field K] [Algebra (ZMod p) K]

def sourceBase : Subfield K := (algebraMap (ZMod p) K).fieldRange

def baseEquiv : Fin p ≃ sourceBase (K := K) :=
  (ZMod.finEquiv p).toEquiv.trans
    (Equiv.ofInjective (algebraMap (ZMod p) K) (RingHom.injective _))

def accepted (w : Word) : Option (sourceBase (K := K)) :=
  if h : w.val % 2^31 < p then some (baseEquiv ⟨w.val % 2^31, h⟩) else none

theorem accepted_failure (w : Word) : accepted (K := K) w = none ↔ rejB w = true := by
  unfold accepted
  rw [rejB_iff]
  have hm := Nat.mod_lt w.val (show 0 < 2^31 by positivity)
  split_ifs with h
  · simp only [reduceCtorEq, false_iff]
    change w.val % 2^31 < 2^31-1 at h
    omega
  · simp only [true_iff]
    change ¬ w.val % 2^31 < 2^31-1 at h
    omega

theorem accepted_fibre (a : sourceBase (K := K)) (w : Word) :
    accepted w = some a ↔ w.val % 2^31 = (baseEquiv.symm a).val := by
  unfold accepted
  split_ifs with h
  · rw [Option.some.injEq, Equiv.apply_eq_iff_eq_symm_apply, Fin.ext_iff]
  · simp only [reduceCtorEq, false_iff]
    intro eq
    have ha := (baseEquiv.symm a).isLt
    rw [eq] at h
    exact h ha

theorem accepted_equal_fibres (a : sourceBase (K := K)) :
    (Finset.univ.filter (fun w : Word => accepted w = some a)).card = 2 := by
  let v := (baseEquiv.symm a).val
  have hv : v < 2^31-1 := (baseEquiv.symm a).isLt
  have eq : (Finset.univ.filter (fun w : Word => accepted w = some a)) =
      {⟨v, by omega⟩, ⟨v + 2^31, by omega⟩} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, accepted_fibre,
      Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    have hw := w.isLt
    change w.val % 2^31 = v ↔ w.val = v ∨ w.val = v + 2^31
    omega
  rw [eq]
  apply Finset.card_pair
  intro same
  have bad := congrArg Fin.val same
  dsimp at bad
  omega

#print axioms baseEquiv
#print axioms accepted_failure
#print axioms accepted_fibre
#print axioms accepted_equal_fibres
end R1Z.ProverCommitWordCarrier
