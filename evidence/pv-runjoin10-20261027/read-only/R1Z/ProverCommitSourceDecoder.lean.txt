import R1Z.ProverCommitSequentialArrays
import R1Z.ProverCommitSourceCarrier
import R1Z.FinalR1PBin

/-! A finite sequential word decoder for the raw source sample families.
Its field law is unconditional; matching its coordinate order to the shipped
caller is deliberately not asserted by these definitions. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSourceDecoder
open R0P R0Z.JointView R0Z.MaskLayout R0Z.FsStatement R1Z.GamesR1PBin
  R1Z.ProverCommitWordCarrier R1Z.ProverCommitSourceCarrier R1Z.ProverCommitTapeCompletion
  R1Z.ProverCommitSequentialFibres R1Z.FinalR1PBin
attribute [local instance] Classical.propDecidable

abbrev Stream1Coord := EligibleCell ⊕ ((Fin 10 × Fin 1024) ⊕
  ((Fin 1024 × Fin 4) ⊕ (FreeRow × Fin 4)))
abbrev Stream2Coord := Fin 1024 × Fin 4
def L₁ : Nat := Fintype.card Stream1Coord
def L₂ : Nat := Fintype.card Stream2Coord
def E₁ : Nat := 2 * L₁
def E₂ : Nat := 2 * L₂

variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)

def streamCarrierEquiv : ((Stream1Coord → F) × (Stream2Coord → F)) ≃ Samples K F where
  toFun s := ((fun c => s.1 (.inl c)), (fun c => s.1 (.inr (.inl c))),
    (fun c => s.1 (.inr (.inr (.inl c)))), (fun c => s.1 (.inr (.inr (.inr c)))), s.2)
  invFun s := ((fun c => match c with
    | .inl c => s.1 c
    | .inr (.inl c) => s.2.1 c
    | .inr (.inr (.inl c)) => s.2.2.1 c
    | .inr (.inr (.inr c)) => s.2.2.2.1 c), s.2.2.2.2)
  left_inv s := by
    apply Prod.ext
    · funext c; rcases c with c | c | c | c <;> rfl
    · rfl
  right_inv s := rfl

def arrayCarrierEquiv : ((Fin L₁ → F) × (Fin L₂ → F)) ≃ SourceTape K F :=
  ((Equiv.prodCongr
    (Equiv.arrowCongr (Fintype.equivFin Stream1Coord).symm (Equiv.refl F))
    (Equiv.arrowCongr (Fintype.equivFin Stream2Coord).symm (Equiv.refl F))).trans
      streamCarrierEquiv).trans sourceCarrierEquiv

abbrev Inputs := (Fin E₁ → OracleAnswer) × (Fin E₂ → OracleAnswer)
def inputEquiv : Inputs ≃ ((Fin (E₁*8) → R1Z.CommitReadsR1.Word) ×
    (Fin (E₂*8) → R1Z.CommitReadsR1.Word)) :=
  Equiv.prodCongr (wordsE E₁) (wordsE E₂)

def quotientDecoder (e : Inputs) : Option (SourceTape K F) :=
  (pairDecode (accepted (K := K)) (E₁*8) (E₂*8) L₁ L₂ (inputEquiv e)).map arrayCarrierEquiv

theorem map_equiv_some {T U : Type} (eqv : T ≃ U) (o : Option T) (u : U) :
    o.map eqv = some u ↔ o = some (eqv.symm u) := by
  cases o with
  | none => simp
  | some t => simpa only [Option.map_some, Option.some.injEq] using eqv.apply_eq_iff_eq_symm_apply

theorem fibre_transport {I J T U : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (q : T ≃ U) (decode : J → Option T) (u : U) :
    (Finset.univ.filter (fun i => (decode (e i)).map q = some u)).card =
      (Finset.univ.filter (fun j => decode j = some (q.symm u))).card := by
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (map_equiv_some q _ u).mp (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ eq
    exact e.injective eq
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (map_equiv_some q _ u).mpr ?_⟩
    simpa only [e.apply_symm_apply] using (Finset.mem_filter.mp hj).2

def quotientFibreSize : Nat :=
  fibreSize (2^32) 2 2 (E₁*8) L₁ 16 * fibreSize (2^32) 2 2 (E₂*8) L₂ 16

theorem rejected_fibre :
    (Finset.univ.filter (fun w : R1Z.CommitReadsR1.Word => accepted (K := K) w = none)).card = 2 := by
  have eq : (Finset.univ.filter (fun w : R1Z.CommitReadsR1.Word => accepted (K := K) w = none)) =
      (Finset.univ.filter (fun w => R1Z.CommitReadsR1.rejB w = true)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, accepted_failure]
  rw [eq, R1Z.CommitReadsR1.card_rej]

attribute [local irreducible] L₁ L₂ E₁ E₂ arrayCarrierEquiv sourceBase

/-- Exact quotient fibres, without an assumed cF or padded-limb decoding. -/
theorem quotient_equal_fibres (s : SourceTape K F) :
    (Finset.univ.filter (fun e : Inputs => quotientDecoder e = some s)).card = quotientFibreSize := by
  have ht := fibre_transport inputEquiv (arrayCarrierEquiv (K := K))
    (pairDecode (accepted (K := K)) (E₁*8) (E₂*8) L₁ L₂) s
  have hp := pair_equal_fibres (accepted (K := K)) 2 2 (rejected_fibre (K := K))
    (fun a => by convert accepted_equal_fibres (K := K) a) (E₁*8) (E₂*8) L₁ L₂ ((arrayCarrierEquiv (K := K)).symm s)
  calc
    _ = (Finset.univ.filter (fun ws => pairDecode (accepted (K := K))
        (E₁*8) (E₂*8) L₁ L₂ ws = some ((arrayCarrierEquiv (K := K)).symm s))).card := by
      convert ht using 1 <;> congr 1 <;> ext z <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, quotientDecoder]
    _ = _ := by
      simpa only [quotientFibreSize, R1Z.CommitReadsR1.Word, Fintype.card_fin] using hp

#print axioms streamCarrierEquiv
#print axioms arrayCarrierEquiv
#print axioms inputEquiv
#print axioms map_equiv_some
#print axioms fibre_transport
#print axioms rejected_fibre
#print axioms quotient_equal_fibres
end R1Z.ProverCommitSourceDecoder
