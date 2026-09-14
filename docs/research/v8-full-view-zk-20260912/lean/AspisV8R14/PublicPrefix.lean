import AspisV8R14.TwoCommitments
import AspisV8H1C2.FiniteTransport
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
Explicit normal form: anchored oracle cells, message/residual coordinates.
The actual source must instantiate phi with its causal R12 equations. No
oracle-query history, opening, or source independence is inferred here.
DRAFT: not compiled in the packet-building environment.
-/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8R14
open AspisV8R13
variable {C V Msg Index Key Digest : Type*} [DecidableEq Key]

def normalCoinEquiv (a b : Index → Key)
    (phi : (Index → Digest) → (Index → Digest) → C ≃ V) :
    TwinWorld C Index Key Digest ≃ TwinWorld V Index Key Digest where
  toFun w := (phi (selected w.2.1 a) (selected w.2.2 b) w.1, w.2)
  invFun w := ((phi (selected w.2.1 a) (selected w.2.2 b)).symm w.1, w.2)
  left_inv w := by rcases w with ⟨c,H1,H2⟩; simp
  right_inv w := by rcases w with ⟨v,H1,H2⟩; simp

def prefixWorldEquiv (first : C → Index → Key)
    (second : C → (Index → Digest) → Index → Key) (a b : Index → Key)
    (phi : (Index → Digest) → (Index → Digest) → C ≃ V) :
    TwinWorld C Index Key Digest ≃ TwinWorld V Index Key Digest :=
  (twoCommitmentEquiv first second a b).trans (normalCoinEquiv a b phi)

def sourcePrefix (first : C → Index → Key)
    (second : C → (Index → Digest) → Index → Key)
    (phi : (Index → Digest) → (Index → Digest) → C ≃ V)
    (render : (Index → Digest) → (Index → Digest) → V → Msg) (w : TwinWorld C Index Key Digest) :=
  let h1 := selected w.2.1 (first w.1)
  let h2 := selected w.2.2 (second w.1 h1)
  (h1,h2,render h1 h2 (phi h1 h2 w.1))

/-- This observation has no witness/offset/payload-function argument. Full
public protocol queries are rendered using the separately fixed remainder
oracle, which may be included in a surrounding fixed context. -/
def publicPrefix (a b : Index → Key) (render : (Index → Digest) → (Index → Digest) → V → Msg)
    (w : TwinWorld V Index Key Digest) :=
  (selected w.2.1 a, selected w.2.2 b,
    render (selected w.2.1 a) (selected w.2.2 b) w.1)

theorem prefix_normalization_commutes (first : C → Index → Key)
    (second : C → (Index → Digest) → Index → Key) (a b : Index → Key)
    (phi : (Index → Digest) → (Index → Digest) → C ≃ V) (render : (Index → Digest) → (Index → Digest) → V → Msg)
    (w : TwinWorld C Index Key Digest) :
    publicPrefix a b render (prefixWorldEquiv first second a b phi w) =
      sourcePrefix first second phi render w := by
  rcases w with ⟨c,H1,H2⟩
  simp [publicPrefix, sourcePrefix, prefixWorldEquiv, twoCommitmentEquiv,
    normalCoinEquiv, normalizeTwo]

noncomputable section
variable [DecidableEq Index]
variable [Fintype C] [Fintype V] [Fintype Index] [Fintype Key] [Fintype Digest]
variable [Nonempty C] [Nonempty V] [Nonempty Digest]

theorem ideal_public_prefix_law (first : C → Index → Key)
    (second : C → (Index → Digest) → Index → Key) (a b : Index → Key)
    (phi : (Index → Digest) → (Index → Digest) → C ≃ V) (render : (Index → Digest) → (Index → Digest) → V → Msg) :
    AspisV8H1C2.SameUniformLaw (sourcePrefix first second phi render)
      (publicPrefix a b render) := by
  apply AspisV8H1C2.sameUniformLaw_of_equiv _ _
    (prefixWorldEquiv first second a b phi)
  exact prefix_normalization_commutes first second a b phi render

#print axioms prefixWorldEquiv
#print axioms prefix_normalization_commutes
#print axioms ideal_public_prefix_law
end
end AspisV8R14
