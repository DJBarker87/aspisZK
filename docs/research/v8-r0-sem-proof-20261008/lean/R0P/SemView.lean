import R0P.SemSource
import R0P.Copy

/-! Lead: the pair-forest semantic messages and the opening view.

Semantic message per round (aspis-core state_only_sumcheck.rs:96–105, 241;
aspis-prover v6_onefold_prover.rs:596–612): nothing before λ, χ, the ten
zerocheck coordinates and μ; the H1 commitment before θ; a round
polynomial before each α_j. The point claims follow α₁₀ and ride on B2's
`beforeZ0` message. The three opening points are α, its polynomial binary
successor and its bit-2/3 toggle (state_only_poseidon.rs:95–117), written
in the source's MSB-first coordinate order; R0's `eqWeight` reads bits
LSB-first, so the view reverses coordinates. -/
set_option autoImplicit false
namespace R0P.SemSource
open FS FS2 R0C.SemStatement Polynomial
open AspisPool.AlgorithmicCircleDecoderV7 AspisV8R19.MemoizedProgramLaw
open AspisR0.Chord AspisR0.ChordGeometry

noncomputable section
attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {Sfield : Fin 29 → Subfield K}

inductive SemMsg (K : Type) [Field K]
  | none
  | h1 (w : InitialWord K)
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
  W : Fin 29 → InitialWord K
  base : ∀ l i, W l i ∈ Sfield l

/-- Challenges of a semantic round list, all scalar. -/
def semChals : List (Msg K K (SemMsg K) × Chal K K) → Option (List K)
  | [] => some []
  | (_, .semantic c) :: rest => (semChals rest).map (c :: ·)
  | _ => Option.none

/-- The opening rounds, all of the opening kind. -/
def openingRounds : List (Msg K K (SemMsg K) × Chal K K) →
    Option (List (R0FS.Msg K × R0FS.Chal K))
  | [] => some []
  | (.opening om, .opening oc) :: rest => (openingRounds rest).map ((om, oc) :: ·)
  | _ => Option.none

/-- The opening statement for a parsed semantic transcript. `semantic` is
`True`: the semantic phase is now explicit in the prefix. -/
def openingStmt (x : TypedContext K Sfield) (α : Fin 10 → K) (y : Fin 3 → Fin 29 → K)
    (z0 z1 : Point K) (hne : z0 ≠ z1) (h0 : ¬ BaseRational z0) (h1 : ¬ BaseRational z1) :
    R0FS.Stmt K Sfield :=
  { W := x.W, base := x.base, z0 := z0, z1 := z1, hne := hne, h0 := h0, h1 := h1,
    points := openingPoints α, pointClaims := y, inactive := copyInactiveRows, semantic := True }

/-- B2's `openingView`: 24 semantic rounds, the two circle rounds, then the
opening rounds. Malformed prefixes have no view. -/
def openingView (P : Prefix K K (TypedContext K Sfield) (SemMsg K)) :
    Option (FS.Prefix (R0FS.Stmt K Sfield) (R0FS.Msg K) (R0FS.Chal K)) :=
  match P.rounds.splitAt 24 with
  | (sem, (.beforeZ0 y, .circle z0) :: (.beforeZ1 _, .circle z1) :: opening) =>
    match semChals sem, openingRounds opening with
    | some cs, some os =>
      if h : cs.length = 24 ∧ z0 ≠ z1 ∧ ¬ BaseRational z0 ∧ ¬ BaseRational z1 then
        some ⟨openingStmt P.statement
          (fun j => cs[14 + j.val]'(by omega)) y z0 z1 h.2.1 h.2.2.1 h.2.2.2, os⟩
      else Option.none
    | _, _ => Option.none
  | _ => Option.none

#print axioms openingView

end
end R0P.SemSource
