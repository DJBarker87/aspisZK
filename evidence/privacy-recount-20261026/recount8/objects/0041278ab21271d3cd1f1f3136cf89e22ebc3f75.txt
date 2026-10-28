import R1Z.ProverCommitSourceSuccess
import R1Z.ProverCommitQuotientStrict

/-! Exact model-to-endpoint law and strictness on the actual two-stream input
carrier. The caller equation below is the still-unproved source frontier. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSourceDecoder
open R0Z.JointView R1Z.ProverCommitTapeCompletion R1Z.ProverCommitWordCarrier
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)
attribute [local irreducible] L₁ L₂ E₁ E₂ arrayCarrierEquiv sourceBase

theorem quotient_premise_of_caller (decode : Inputs → Option (Tape K F))
    (caller : ∀ e, quotientDecode decode e = quotientDecoder e) (s : SourceTape K F) :
    (Finset.univ.filter (fun e => quotientDecode decode e = some s)).card = quotientFibreSize := by
  have eq := funext caller
  rw [eq]
  convert quotient_equal_fibres (K := K) s

def representativeDecoder (e : Inputs) : Option (Tape K F) :=
  (quotientDecoder e).map (fun s => complete s 0)

theorem representative_quotient (e : Inputs) :
    quotientDecode (representativeDecoder (K := K)) e = quotientDecoder e := by
  cases hs : quotientDecoder (K := K) e <;>
    simp only [quotientDecode, representativeDecoder, hs, Option.map_none, Option.map_some, project_complete]

/-- A strictness witness on the same byte-block inputs as the protocol. -/
theorem source_representative_not_full_fibres [Fintype K] :
    ¬ ∃ c : Nat, ∀ t : Tape K F,
      (Finset.univ.filter (fun e : Inputs => representativeDecoder e = some t)).card = c := by
  rintro ⟨c,uniform⟩
  obtain ⟨input,s,success⟩ := decoder_has_success (K := K)
  obtain ⟨missing,absent⟩ := section_missing (fun _ : SourceTape K F => 0) s
  have not_image : ∀ e : Inputs, representativeDecoder (K := K) e ≠ some missing := by
    intro e eq
    cases hs : quotientDecoder (K := K) e with
    | none => simp only [representativeDecoder, hs, Option.map_none, reduceCtorEq] at eq
    | some q =>
      have same : complete q 0 = missing := Option.some.inj (by
        simpa only [representativeDecoder, hs, Option.map_some] using eq)
      exact absent q same
  have empty : (Finset.univ.filter (fun e : Inputs => representativeDecoder (K := K) e = some missing)) = ∅ := by
    ext e
    simp [not_image e]
  have zero : c = 0 := by
    have eq := uniform missing
    rw [empty, Finset.card_empty] at eq
    exact eq.symm
  have positive : 0 < (Finset.univ.filter (fun e : Inputs =>
      representativeDecoder (K := K) e = some (complete s 0))).card := by
    apply Finset.card_pos.mpr
    exact ⟨input, by simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      representativeDecoder, success, Option.map_some]⟩
  rw [uniform, zero] at positive
  exact (Nat.lt_irrefl 0) positive

#print axioms quotient_premise_of_caller
#print axioms representative_quotient
#print axioms source_representative_not_full_fibres
end R1Z.ProverCommitSourceDecoder
