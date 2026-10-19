import DecodedFirstReadTraceBridge
import RawCutProverCompiler

/-! The recording compiler's verifier replay cannot create new decoder-start
opportunities. This preserves the sharpened probability budget, for any causal
decoder, as well as the previously proved total-query budget. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DecodedFirstReadUnionBound
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
variable {X M C I A Y : Type} [DecidableEq I]
attribute [local instance] Classical.propDecidable

def applyTrace (t : Table I A) : List (I × A) → Table I A
  | [] => t
  | (i,a)::rest => applyTrace (put t i a) rest

private theorem applyTrace_preserves_present (t : Table I A)
    (tr : List (I × A)) (key : I) (hk : t key ≠ none) :
    applyTrace t tr key ≠ none := by
  induction tr generalizing t with
  | nil => exact hk
  | cons cell rest ih =>
    rcases cell with ⟨i,a⟩
    apply ih
    by_cases h : key = i
    · subst key
      simp [put]
    · simpa [put, h] using hk

private theorem applyTrace_present_of_read (t : Table I A)
    (tr : List (I × A)) (key : I) (hr : key ∈ tr.map Prod.fst) :
    applyTrace t tr key ≠ none := by
  induction tr generalizing t with
  | nil => simp at hr
  | cons cell rest ih =>
    rcases cell with ⟨i,a⟩
    simp only [List.map_cons, List.mem_cons] at hr
    rcases hr with h | h
    · subst key
      exact applyTrace_preserves_present (put t i a) rest i (by simp [put])
    · exact ih (put t i a) h

theorem decoderFirstReads_append (dec : Dec X M C I A Y)
    (t : Table I A) (pre tail : List (I × A)) :
    decoderFirstReads dec t (pre ++ tail) =
      decoderFirstReads dec t pre + decoderFirstReads dec (applyTrace t pre) tail := by
  induction pre generalizing t with
  | nil => simp [decoderFirstReads, applyTrace]
  | cons cell rest ih =>
    rcases cell with ⟨i,a⟩
    simp only [List.cons_append, decoderFirstReads, applyTrace]
    rw [ih]
    omega

private theorem decoderFirstReads_zero_of_present (dec : Dec X M C I A Y)
    (t : Table I A) (tr : List (I × A))
    (hp : ∀ key ∈ tr.map Prod.fst, t key ≠ none) :
    decoderFirstReads dec t tr = 0 := by
  induction tr generalizing t with
  | nil => rfl
  | cons cell rest ih =>
    rcases cell with ⟨i,a⟩
    have hi : t i ≠ none := hp i (by simp)
    have htail : ∀ key ∈ rest.map Prod.fst, put t i a key ≠ none := by
      intro key hkey
      by_cases heq : key = i
      · subst key
        simp [put]
      · simpa [put, heq] using hp key (by simp [hkey])
    simp only [decoderFirstReads, hi, false_and, if_false, zero_add]
    exact ih (put t i a) htail

theorem decoderFirstReads_append_reused (dec : Dec X M C I A Y)
    (pre replay : List (I × A))
    (hread : ∀ key ∈ replay.map Prod.fst, key ∈ pre.map Prod.fst) :
    decoderFirstReads dec emptyTable (pre ++ replay) =
      decoderFirstReads dec emptyTable pre := by
  rw [decoderFirstReads_append]
  have hz : decoderFirstReads dec (applyTrace emptyTable pre) replay = 0 :=
    decoderFirstReads_zero_of_present dec _ _ (fun key hk =>
      applyTrace_present_of_read emptyTable pre key (hread key hk))
  rw [hz, Nat.add_zero]

theorem decoderFirstReads_repeat_suffix (dec : Dec X M C I A Y)
    (pre tail : List (I × A)) :
    decoderFirstReads dec emptyTable ((pre ++ tail) ++ tail) =
      decoderFirstReads dec emptyTable (pre ++ tail) := by
  apply decoderFirstReads_append_reused
  intro key hk
  simp only [List.map_append, List.mem_append]
  exact Or.inr hk

#print axioms decoderFirstReads_append
#print axioms decoderFirstReads_append_reused
#print axioms decoderFirstReads_repeat_suffix
end AspisR1.DecodedFirstReadUnionBound
end
