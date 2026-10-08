import R0P.CopyRegistry
import R0P.LogUpFrac
import R0P.LogUpCompress
import R0P.SemBadSets
import R0P.SemAssembly

/-! Lead: the LogUp assembly's objects and bad set, and the glue.

For a fixed trace `t`, variant/index `pub`, challenges `lam`, `chi`:
enabled links (weight ≠ 0), their compressed producer/consumer values,
the finset `D` of those values, the signed count `m v` (producers minus
consumers at value v, cast to K), the multisets `S`, `T` of tagged-tuple
compression polynomials, and the bad set `BadLogUp` (ledger branches
activePole incl. χ = 0, copyChi, tupleCompression). The chain L1–L5 is
stated as named Props; `logup_step_of` glues them into `LogUpStep`. -/
set_option autoImplicit false
namespace R0P
open Polynomial Sumcheck

variable {K : Type} [Field K]

noncomputable section
open Classical

def enabledLinks (pub : Public K) : List CopyLink := copyLinks.filter (copyLinkEnabled pub)

def prodVal (t : Trace K) (lam : K) (link : CopyLink) : K :=
  copyTupleValue lam (copyProducerTuple t link)
def consVal (t : Trace K) (lam : K) (link : CopyLink) : K :=
  copyTupleValue lam (copyConsumerTuple t link)

/-- Distinct enabled compressed values. -/
def valueSet (pub : Public K) (t : Trace K) (lam : K) : Finset K :=
  ((enabledLinks pub).map (prodVal t lam) ++ (enabledLinks pub).map (consVal t lam)).toFinset

/-- All endpoint values, enabled or not: a disabled slot still contributes
its factor `χ − value` to the row residual (logup.rs:228–252), so it is a
pole. -/
def poleSet (t : Trace K) (lam : K) : Finset K :=
  (copyLinks.map (prodVal t lam) ++ copyLinks.map (consVal t lam)).toFinset

theorem valueSet_subset_poleSet (pub : Public K) (t : Trace K) (lam : K) :
    valueSet pub t lam ⊆ poleSet t lam := by
  intro v hv
  simp only [valueSet, poleSet, List.mem_toFinset, List.mem_append, List.mem_map,
    enabledLinks, List.mem_filter] at hv ⊢
  rcases hv with ⟨l, ⟨hl, _⟩, rfl⟩ | ⟨l, ⟨hl, _⟩, rfl⟩
  · exact Or.inl ⟨l, hl, rfl⟩
  · exact Or.inr ⟨l, hl, rfl⟩

/-- Producers minus consumers at value `v`. -/
def signedCount (pub : Public K) (t : Trace K) (lam : K) (v : K) : K :=
  ((((enabledLinks pub).filter (fun l => prodVal t lam l = v)).length : Nat) : K) -
    ((((enabledLinks pub).filter (fun l => consVal t lam l = v)).length : Nat) : K)

def prodPolys (pub : Public K) (t : Trace K) : Multiset K[X] :=
  ((enabledLinks pub).map (fun l => compressPoly (copyProducerTuple t l)) : List K[X])
def consPolys (pub : Public K) (t : Trace K) : Multiset K[X] :=
  ((enabledLinks pub).map (fun l => compressPoly (copyConsumerTuple t l)) : List K[X])

/-- Ledger branches activePole (with χ = 0 for empty slots), copyChi and
tupleCompression. The λ branch is the root set of a nonzero coefficient of
`Π(X − P) − Π(X − Q)` over K[λ]. -/
def BadLogUp (pub : Public K) (t : Trace K) (lam chi : K) : Prop :=
  chi = 0 ∨ chi ∈ poleSet t lam ∨
  (numer (valueSet pub t lam) (signedCount pub t lam) ≠ 0 ∧
    (numer (valueSet pub t lam) (signedCount pub t lam)).eval chi = 0) ∨
  (prodPolys pub t ≠ consPolys pub t ∧
    ∃ k, ((((prodPolys pub t).map (fun q => X - C q)).prod -
      ((consPolys pub t).map (fun q => X - C q)).prod).coeff k) ≠ 0 ∧
      ((((prodPolys pub t).map (fun q => X - C q)).prod -
        ((consPolys pub t).map (fun q => X - C q)).prod).coeff k).eval lam = 0)

/-- L1: off poles, the row identity is the helper's fraction form. -/
def LogUpL1 (pub : Public K) (t : Trace K) (lam chi : K) : Prop :=
  chi ≠ 0 → chi ∉ poleSet t lam → CHolds copyFamily pub lam chi t →
    ∀ b : Fin 1024, CopyActiveRow b →
      t 26 b = ((enabledLinks pub).filter (fun l => l.producer.row = b)).foldr
          (fun l acc => acc + 1 / (chi - prodVal t lam l)) 0 -
        ((enabledLinks pub).filter (fun l => l.consumer.row = b)).foldr
          (fun l acc => acc + 1 / (chi - consVal t lam l)) 0

/-- L2: both helper sums zero gives the aggregated fraction identity. -/
def LogUpL2 (pub : Public K) (t : Trace K) (lam chi : K) : Prop :=
  chi ∉ valueSet pub t lam →
    (∀ b : Fin 1024, CopyActiveRow b →
      t 26 b = ((enabledLinks pub).filter (fun l => l.producer.row = b)).foldr
          (fun l acc => acc + 1 / (chi - prodVal t lam l)) 0 -
        ((enabledLinks pub).filter (fun l => l.consumer.row = b)).foldr
          (fun l acc => acc + 1 / (chi - consVal t lam l)) 0) →
    (∑ b : Fin 1024, t 26 b) = 0 → (∑ b ∈ copyInactiveRows, t 26 b) = 0 →
    ∑ v ∈ valueSet pub t lam, signedCount pub t lam v / (chi - v) = 0

/-- L3 (G6): off the numerator's roots, the aggregated identity is balance. -/
def LogUpL3 (pub : Public K) (t : Trace K) (lam chi : K) : Prop :=
  chi ∉ valueSet pub t lam →
    ¬ (numer (valueSet pub t lam) (signedCount pub t lam) ≠ 0 ∧
      (numer (valueSet pub t lam) (signedCount pub t lam)).eval chi = 0) →
    (∑ v ∈ valueSet pub t lam, signedCount pub t lam v / (chi - v)) = 0 →
    ∀ v ∈ valueSet pub t lam, signedCount pub t lam v = 0

/-- L4 (G7, G10): balance of values at λ outside the coefficient roots is
equality of the tuple-polynomial multisets. -/
def LogUpL4 (pub : Public K) (t : Trace K) (lam : K) : Prop :=
  (∀ v ∈ valueSet pub t lam, signedCount pub t lam v = 0) →
    ¬ (prodPolys pub t ≠ consPolys pub t ∧
      ∃ k, ((((prodPolys pub t).map (fun q => X - C q)).prod -
        ((consPolys pub t).map (fun q => X - C q)).prod).coeff k) ≠ 0 ∧
        ((((prodPolys pub t).map (fun q => X - C q)).prod -
          ((consPolys pub t).map (fun q => X - C q)).prod).coeff k).eval lam = 0) →
    prodPolys pub t = consPolys pub t

/-- L5 (G5, G7): equal multisets with distinct tags give per-link equality. -/
def LogUpL5 (pub : Public K) (t : Trace K) : Prop :=
  prodPolys pub t = consPolys pub t → CopyLinkBalance pub t

theorem logup_step_of (pub : Public K) (t : Trace K)
    (h1 : ∀ lam chi, LogUpL1 pub t lam chi) (h2 : ∀ lam chi, LogUpL2 pub t lam chi)
    (h3 : ∀ lam chi, LogUpL3 pub t lam chi) (h4 : ∀ lam, LogUpL4 pub t lam)
    (h5 : LogUpL5 pub t)
    (H1 inact : (Fin 10 → Bool) → K)
    (hS1 : bsumB 10 H1 = ∑ b : Fin 1024, t 26 b)
    (hS2 : bsumB 10 inact = ∑ b ∈ copyInactiveRows, t 26 b) :
    LogUpStep pub t (BadLogUp pub t) H1 inact := by
  intro lam chi hbad hc hs1 hs2
  simp only [BadLogUp, not_or] at hbad
  obtain ⟨h0, hP, hnum, hlam⟩ := hbad
  have hD : chi ∉ valueSet pub t lam := fun h => hP (valueSet_subset_poleSet t lam h)
  rw [hS1] at hs1
  rw [hS2] at hs2
  have hrows := h1 lam chi h0 hP hc
  have hfrac := h2 lam chi hD hrows hs1 hs2
  have hbal := h3 lam chi hD hnum hfrac
  exact h5 (h4 lam hbal hlam)

#print axioms logup_step_of
end
end R0P
