import R0Z.D12
import R0Z.Shift

/-! Z4 opening move only: observation maps and unproved surjectivity targets.
The targets below are propositions, not asserted theorems or certificates.
No rank computation or unrestricted ambient-surjectivity claim is made. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.Z4Maps
open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12 R0Z.Shift
attribute [local instance] Classical.propDecidable
variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [BatchedLayer K Bat]

def roundProjection : Payload K Bat →ₗ[F] PayloadSplit.RoundPayload K :=
  LinearMap.pi fun j => LinearMap.pi fun i => LinearMap.proj (.semanticCoeff j i)

/-- A ∘ inl_M observed on the round-polynomial component. -/
def roundMaskMap (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) :
    M K F →ₗ[F] PayloadSplit.RoundPayload K :=
  roundProjection.comp ((A (Bat := Bat) π B ch).comp inlM)

/-- (i) requires zero change to every non-round disclosure. Projection alone
would forget that requirement, so its lift must lie in this kernel. -/
def silentMasks (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) : Submodule F (M K F) :=
  LinearMap.ker (nonRound.comp ((A (Bat := Bat) π B ch).comp inlM))

def silentRoundMaskMap (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) :
    silentMasks (Bat := Bat) π B ch →ₗ[F] PayloadSplit.RoundPayload K :=
  (roundMaskMap (Bat := Bat) π B ch).comp (silentMasks π B ch).subtype

inductive C1Cell
  | point (j : Fin 3) (c : Fin 16)
  | ood (j : Fin 2) (c : Fin 16)
  | opened (q : Fin 262144) (s : Fin 4) (c : Fin 16)
  deriving DecidableEq, Fintype

/-- Exactly the semantic C1 claims and query-gated openings. -/
def c1Projection : Payload K Bat →ₗ[F] (C1Cell → K) :=
  LinearMap.pi fun coord => match coord with
  | .point j c => LinearMap.proj (.pointClaim j (Fin.castLE (by omega) c))
  | .ood j c => LinearMap.proj (.ood j (Fin.castLE (by omega) c))
  | .opened q s c => LinearMap.proj (.opened q s (Fin.castLE (by omega) c))

/-- Full joint tape observed in the C1 components that the pure masks cannot hide. -/
def c1Map (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) : T K F →ₗ[F] (C1Cell → K) :=
  c1Projection.comp (A (Bat := Bat) π B ch)

/-- Z4 lemma statement for (i′) on `Good`, including the zero-complement
constraint: the target is the round projection of D14's remainder s(w,n) after
Ψ_ch, not the entire ambient array. -/
def roundMask_surjectivity (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) : Prop :=
  ∀ ch, Good ch → ∀ w n, h.public w = x.1 →
    ∃ m : silentMasks (Bat := Bat) h.transport B ch,
      silentRoundMaskMap h.transport B ch m = roundProjection (F := F) (sRem (Bat := Bat) h B x w ch n)

/-- Z4 encoder-restriction lemma statement needed for (ii) beyond the mask
lanes. This is the C1 part only: a proof still needs a compatible lift for the
remaining components before it can establish full-payload clause (ii′). Its C1
projection does not see `dir`, so only the `Good` restriction is added. -/
def c1_surjectivity (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) : Prop :=
  ∀ ch, Good ch → ∀ w w', h.public w = x.1 → h.public w' = x.1 →
    c1Projection (F := F) (c (Bat := Bat) h B x w ch - c h B x w' ch) ∈ LinearMap.range (c1Map (Bat := Bat) h.transport B ch)

#print roundMask_surjectivity
#print c1_surjectivity
#print axioms roundMaskMap
#print axioms silentRoundMaskMap
#print axioms c1Map
end R0Z.Z4Maps
