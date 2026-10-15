import R1MatchingSupport
import Wide.SubfieldDescentCore

/-! The literal R1 list already contains only subfield-typed candidates when
its committed words are typed. This reuses the existing exact decoder and
Galois-descent theorems; candidate typing is derived, not assumed separately.
It does not identify committed words with parsed bytes or prove semantics. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace AspisR1.CandidateDescent

open AspisCircleGroupOrder AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.SubfieldDescent
open AspisV6Width29CorrelatedAgreement

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

def WordTyped (S : Fin 29 → Subfield E) (W : Fin 29 → InitialWord E) : Prop :=
  ∀ l i, W l i ∈ S l

def MessageTyped (S : Fin 29 → Subfield E)
    (t : AspisR1.ConcreteBinding.Tuple E) : Prop :=
  ∀ l r, t l r ∈ S l

theorem candidate_codeword_typed
    (S : Fin 29 → Subfield E) (W : Fin 29 → InitialWord E)
    (typed : WordTyped S W) (t : AspisR1.ConcreteBinding.Tuple E)
    (ht : t ∈ AspisR1.ConcreteBinding.candidates W) :
    ∀ l i, exactInitialEncoder (t l) i ∈ S l := by
  classical
  have hcard : 38230 ≤ (width29JointAgreementSet exactInitialEncoder W t).card :=
    (AspisR1.InitialResponses.mem_Lambda W t).mp ht
  intro l
  apply initialCodeword_subfield_descent (S l) (W l) (t l)
    (width29JointAgreementSet exactInitialEncoder W t) (by omega)
  · intro i hi
    have h := (Finset.mem_filter.mp hi).2
    exact (h l).symm
  · exact typed l

theorem candidate_message_typed
    (S : Fin 29 → Subfield E) (W : Fin 29 → InitialWord E)
    (typed : WordTyped S W) (t : AspisR1.ConcreteBinding.Tuple E)
    (ht : t ∈ AspisR1.ConcreteBinding.candidates W) : MessageTyped S t := by
  intro l
  exact initialMessage_subfield_descent (S l) (t l)
    (candidate_codeword_typed S W typed t ht l)

/-- The semantic rows keep each lane's subfield under any coefficient transport. -/
theorem candidate_rows_typed
    (S : Fin 29 → Subfield E) (W : Fin 29 → InitialWord E)
    (typed : WordTyped S W) (t : AspisR1.ConcreteBinding.Tuple E)
    (ht : t ∈ AspisR1.ConcreteBinding.candidates W)
    (π : Fin 1024 ≃ Fin 1024) : ∀ l r, t l (π r) ∈ S l := by
  intro l r
  exact candidate_message_typed S W typed t ht l (π r)

def TypedClaims (S : Fin 29 → Subfield E)
    (d : AspisR1.MatchingSupport.Data E) : Prop :=
  ∃ t ∈ AspisR1.ConcreteBinding.candidates d.W,
    MessageTyped S t ∧
    (∀ j : Fin 6, ∀ l : Fin 29, d.F j (t l) = d.Y j l) ∧
    d.F0 (AspisR1.ConcreteBinding.batches d.gamma t) = d.c0

theorem claims_iff_typed (S : Fin 29 → Subfield E)
    (d : AspisR1.MatchingSupport.Data E) (typed : WordTyped S d.W) :
    AspisR1.MatchingSupport.Claims d ↔ TypedClaims S d := by
  constructor
  · rintro ⟨t, ht, hrows, hbase⟩
    exact ⟨t, ht, candidate_message_typed S d.W typed t ht, hrows, hbase⟩
  · rintro ⟨t, ht, _, hrows, hbase⟩
    exact ⟨t, ht, hrows, hbase⟩

theorem large_matching_implies_typed_claims
    (S : Fin 29 → Subfield E) (d : AspisR1.MatchingSupport.Data E)
    (typed : WordTyped S d.W)
    (hgood : AspisR1.MatchingSupport.Good d)
    (haccepted : AspisR1.MatchingSupport.AcceptedPairing d)
    (hcard : 9558 ≤ (AspisR1.MatchingSupport.matchingSet d).card) :
    TypedClaims S d :=
  (claims_iff_typed S d typed).mp
    (AspisR1.MatchingSupport.large_matching_implies_claims d hgood haccepted hcard)

#print axioms candidate_codeword_typed
#print axioms candidate_message_typed
#print axioms candidate_rows_typed
#print axioms claims_iff_typed
#print axioms large_matching_implies_typed_claims
end AspisR1.CandidateDescent
end
