import R0P.SemSource
import R0P.Copy

/-! Lead: the pair-forest semantic messages and the opening view.

Semantic message per round (aspis-core state_only_sumcheck.rs:96–105, 241;
aspis-prover v6_onefold_prover.rs:596–612): nothing before λ, χ, the ten
zerocheck coordinates and μ; the H1 commitment before θ; a round
polynomial before each α_j. The point claims follow α₁₀ and ride on B2's
`beforeZ0` message. The C2 commitment (state_only_candidate_prefix.rs:521,
the words `(h1, G)`, lanes 26 and 27) is the message of round 2: the
opening statement's words are the context's with lanes 26/27 replaced by
the parsed C2 words, so the λ/χ rounds precede the C2 choice. The parsers
require the `.semantic` message tag at every semantic round. The three opening points are α, its polynomial binary
successor and its bit-2/3 toggle (state_only_poseidon.rs:95–117), written
in the source's MSB-first coordinate order; R0's `eqWeight` reads bits
LSB-first, so the view reverses coordinates. -/
set_option autoImplicit false
namespace R0P.SemSource
open FS FS2 R0C.SemStatement Polynomial
open AspisPool.AlgorithmicCircleDecoderV7 AspisV8R19.MemoizedProgramLaw
open AspisR0.Chord AspisR0.ChordGeometry AspisWide.InitialEncoder

noncomputable section
attribute [local instance] Classical.propDecidable

section Transport
variable {K : Type} [Field K]
open AspisR0.Opening AspisPool.AlgorithmicCircleDecoderV7

/-- Semantic rows reindexed as commitment coefficients. -/
def coeffsOf (π : Fin 1024 ≃ Fin 1024) (t : Trace K) : Fin 29 → InitialMessage K :=
  fun c j => t c (π.symm j)

def rowsOf (π : Fin 1024 ≃ Fin 1024) (m : Fin 29 → InitialMessage K) : Trace K :=
  fun c r => m c (π r)

@[simp] theorem rowsOf_coeffsOf (π : Fin 1024 ≃ Fin 1024) (t : Trace K) :
    rowsOf π (coeffsOf π t) = t := by
  funext c r
  simp only [rowsOf, coeffsOf, Equiv.symm_apply_apply]

@[simp] theorem coeffsOf_rowsOf (π : Fin 1024 ≃ Fin 1024) (m : Fin 29 → InitialMessage K) :
    coeffsOf π (rowsOf π m) = m := by
  funext c j
  simp only [rowsOf, coeffsOf, Equiv.apply_symm_apply]

def rowsEquiv (π : Fin 1024 ≃ Fin 1024) : (Fin 29 → InitialMessage K) ≃ Trace K where
  toFun := rowsOf π
  invFun := coeffsOf π
  left_inv := coeffsOf_rowsOf π
  right_inv := rowsOf_coeffsOf π

/-- The pre-C2 trace, with the two not-yet-committed message lanes zeroed. -/
def padC2Trace (t : Trace K) : Trace K :=
  Function.update (Function.update t 26 0) 27 0

theorem coeffsOf_padC2Trace (π : Fin 1024 ≃ Fin 1024) (t : Trace K) :
    coeffsOf π (padC2Trace t) = padC2Trace (coeffsOf π t) := by
  funext c j
  simp only [coeffsOf, padC2Trace, Function.update_apply]
  split_ifs <;> rfl

/-- Coefficient-indexed Libra row, shared with the later masked protocol. -/
def libraWeight (alpha : Fin 10 → K) : InitialMessage K := fun j =>
  if j.val < 28 then alpha 8 ^ j.val
  else if j.val < 56 then alpha 9 ^ (j.val - 28) else 0
end Transport

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {Sfield : Fin 29 → Subfield K}

open AspisR0.Opening AspisR0.ListsResponses AspisR0.RoundNormalization
attribute [local irreducible] Lambda

theorem dot_coeffWeight_coeffsOf (π : Fin 1024 ≃ Fin 1024) (w : InitialMessage K)
    (t : Trace K) (c : Fin 29) :
    dot (coeffWeight π w) (coeffsOf π t c) = dot w (t c) := by
  rw [dot_coeffWeight_left]
  simp only [coeffsOf, Equiv.symm_apply_apply]

def LambdaRows (π : Fin 1024 ≃ Fin 1024) (W : Fin 29 → InitialWord K) : Finset (Trace K) :=
  (Lambda W).map (rowsEquiv π).toEmbedding

@[simp] theorem mem_LambdaRows (π : Fin 1024 ≃ Fin 1024) (W : Fin 29 → InitialWord K)
    (t : Trace K) : t ∈ LambdaRows π W ↔ coeffsOf π t ∈ Lambda W := by
  change t ∈ (Lambda W).map (rowsEquiv π).toEmbedding ↔ coeffsOf π t ∈ Lambda W
  constructor
  · intro h
    obtain ⟨m, hm, he⟩ := Finset.mem_map.mp h
    change rowsOf π m = t at he
    rw [← he, coeffsOf_rowsOf]
    exact hm
  · intro h
    exact Finset.mem_map.mpr ⟨coeffsOf π t, h, rowsOf_coeffsOf π t⟩

theorem card_LambdaRows (π : Fin 1024 ≃ Fin 1024) (W : Fin 29 → InitialWord K) :
    (LambdaRows π W).card = (Lambda W).card := Finset.card_map _

theorem LambdaRows_card (π : Fin 1024 ≃ Fin 1024) (W : Fin 29 → InitialWord K) :
    (LambdaRows π W).card ≤ 100 := by
  rw [card_LambdaRows]
  exact Lambda_card W

inductive SemMsg (K : Type) [Field K]
  | none
  /-- the C2 commitment: the words of lanes 26 (H1) and 27 (G) -/
  | h1 (h g : InitialWord K)
  | roundPoly (p : K[X])

/-- state_only_poseidon.rs:95–105: carry after processing k coordinates
from the right (coordinate 9 is the row's least significant bit). -/
def succCarry (p : Fin 10 → K) : Nat → K
  | 0 => 1
  | k+1 => (if h : k < 10 then p ⟨9 - k, by omega⟩ else 0) * succCarry p k

def successorPoint (p : Fin 10 → K) (c : Fin 10) : K :=
  let carry := succCarry p (9 - c.val)
  p c + carry - (p c * carry + p c * carry)

/-- state_only_poseidon.rs:109–117: toggle row bits 2 and 3 (coordinates 7, 6). -/
def xor12Point (p : Fin 10 → K) (c : Fin 10) : K :=
  if c.val = 7 ∨ c.val = 6 then 1 - p c else p c

/-- Source MSB-first coordinates to R0's LSB-first `eqWeight` bits. -/
def toR0 (p : Fin 10 → K) : Fin 10 → K := fun b => p ⟨9 - b.val, by omega⟩

def openingPoints (α : Fin 10 → K) : Fin 3 → Fin 10 → K
  | 0 => toR0 α
  | 1 => toR0 (successorPoint α)
  | 2 => toR0 (xor12Point α)

/-- The committed words with their subfield typing. -/
structure TypedContext (K : Type) [Field K] (Sfield : Fin 29 → Subfield K) where
  pub : Public K
  transport : Fin 1024 ≃ Fin 1024
  extraClaims : Fin 29 → K
  W : Fin 29 → InitialWord K
  base : ∀ l i, W l i ∈ Sfield l
  /-- the common field of definition of the C1 lanes (M31 in the source) -/
  F : Subfield K
  lanesF : ∀ l : Fin 29, l.val < 26 → Sfield l = F
  /-- the public fields are M31 values (CoreExt.PublicBase) -/
  pubBase : PublicBase F pub

/-- The codeword of the zero message: the lane-26/27 placeholder before C2. -/
def padWord : InitialWord K := exactInitialEncoder (fun _ => 0)

/-- The context's words with the C2 words at lanes 26 and 27. -/
def c2Words (x : TypedContext K Sfield) (h g : InitialWord K) : Fin 29 → InitialWord K :=
  Function.update (Function.update x.W 26 h) 27 g

/-- The C2 words are committed in their lanes' fields. -/
def c2Base (Sfield : Fin 29 → Subfield K) (h g : InitialWord K) : Prop :=
  (∀ i, h i ∈ Sfield 26) ∧ (∀ i, g i ∈ Sfield 27)

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem c2Words_base (x : TypedContext K Sfield) (h g : InitialWord K)
    (hb : c2Base Sfield h g) : ∀ l i, c2Words x h g l i ∈ Sfield l := by
  intro l i
  simp only [c2Words, Function.update_apply]
  split_ifs with h27 h26
  · subst h27; exact hb.2 i
  · subst h26; exact hb.1 i
  · exact x.base l i

/-- The C2 words of a semantic round list: the message of round 2. -/
def c2Of (rounds : List (Msg K K (SemMsg K) × Chal K K)) : Option (InitialWord K × InitialWord K) :=
  match (rounds[2]? : Option (Msg K K (SemMsg K) × Chal K K)) with
  | some (Msg.semantic (SemMsg.h1 h g), _) => some (h, g)
  | _ => Option.none

/-- Challenges of a semantic round list, all scalar, with semantic messages. -/
def semChals : List (Msg K K (SemMsg K) × Chal K K) → Option (List K)
  | [] => some []
  | (.semantic _, .semantic c) :: rest => (semChals rest).map (c :: ·)
  | _ => Option.none

/-- The opening rounds, all of the opening kind. -/
def openingRounds : List (Msg K K (SemMsg K) × Chal K K) →
    Option (List (R0FS.Msg K × R0FS.Chal K))
  | [] => some []
  | (.opening om, .opening oc) :: rest => (openingRounds rest).map ((om, oc) :: ·)
  | _ => Option.none

/-- The opening statement for a parsed semantic transcript. `semantic` is
`True`: the semantic phase is now explicit in the prefix. -/
def openingStmt (x : TypedContext K Sfield) (h g : InitialWord K) (hb : c2Base Sfield h g)
    (α : Fin 10 → K) (y : Fin 3 → Fin 29 → K)
    (z0 z1 : Point K) (hne : z0 ≠ z1) (h0 : ¬ BaseRational z0) (h1 : ¬ BaseRational z1) :
    R0FS.Stmt K Sfield :=
  { W := c2Words x h g, base := c2Words_base x h g hb, z0 := z0, z1 := z1, hne := hne, h0 := h0, h1 := h1,
    points := openingPoints α, pointClaims := y, inactive := copyInactiveRows, transport := x.transport,
    extraWeight := libraWeight α, extraClaims := x.extraClaims, semantic := True }

/-- B2's `openingView`: 24 semantic rounds, the two circle rounds, then the
opening rounds. Malformed prefixes have no view. -/
def openingView (P : Prefix K K (TypedContext K Sfield) (SemMsg K)) :
    Option (FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K)) :=
  match P.rounds.splitAt 24 with
  | (sem, (.beforeZ0 y, .circle z0) :: (.beforeZ1 _, .circle z1) :: opening) =>
    match semChals sem, c2Of sem, openingRounds opening with
    | some cs, some (hw, gw), some os =>
      if h : cs.length = 24 ∧ c2Base Sfield hw gw ∧ z0 ≠ z1 ∧ ¬ BaseRational z0 ∧
          ¬ BaseRational z1 then
        some ⟨openingStmt P.statement hw gw h.2.1
          (fun j => cs[14 + j.val]'(by omega)) y z0 z1 h.2.2.1 h.2.2.2.1 h.2.2.2.2, os⟩
      else Option.none
    | _, _, _ => Option.none
  | _ => Option.none

#print axioms c2Words_base
#print axioms openingView

end
end R0P.SemSource
