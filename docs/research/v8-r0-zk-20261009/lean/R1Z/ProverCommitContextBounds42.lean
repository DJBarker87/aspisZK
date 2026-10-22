import R1Z.ProverCommitPrivateBounds42

/-! The fixed-context bound is integrated with its context indicator. No
conditioning division, nonce law, or assumption of a nonempty fiber is used. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitContextBounds42
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
open GamesR1 GamesR1PBin CouplingR1PBin EventsR1PBin LayoutR1PBin LensR1 LazyFrozen
open ProverCommitPrivateBounds42
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (h : HonestProver K) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (w : h.Instance)

theorem context_frozen_mass (hb : RCommitBytes W Pr)
    {C : Type} [Fintype C] [Nonempty C] (gate : C → Prop)
    (nonce : C → NZ) (digest first second : C → OracleAnswer)
    (c : CPos Pr.E₁ Pr.E₂) (hc : privatePos W Pr c) {q : Nat}
    (inputs : C → Fin q → List UInt8) :
    mass (fun r : C × Carrier W Pr => gate r.1 ∧ ∃ i, inputs r.1 i =
      address W Pr h B outputs x w (nonce r.1) (digest r.1) (first r.1) (second r.1) r.2 c) ≤
      mass gate * (q / (2 : ℚ)^255) := by
  rw [mass_prod]
  change mean (fun ctx => mass (fun a : Carrier W Pr => gate ctx ∧ ∃ i, inputs ctx i =
    address W Pr h B outputs x w (nonce ctx) (digest ctx) (first ctx) (second ctx) a c)) ≤ _
  have point (ctx : C) : mass (fun a : Carrier W Pr => gate ctx ∧ ∃ i, inputs ctx i =
      address W Pr h B outputs x w (nonce ctx) (digest ctx) (first ctx) (second ctx) a c) ≤
      (if gate ctx then (1 : ℚ) else 0) * (q / (2 : ℚ)^255) := by
    by_cases hg : gate ctx
    · simp only [hg,true_and,if_true,one_mul]
      exact frozen_mass W Pr h B outputs x w hb (nonce ctx) (digest ctx) (first ctx) (second ctx) c hc (inputs ctx)
    · simp only [hg,false_and,if_false,zero_mul,mass_false]
      exact le_refl _
  have bound := R0Z.FsGood.mean_le_mean _ _ point
  simpa only [mean_mul_const,mass] using bound

/-- The actual global answer-vector projection is the private carrier used
in the preceding mass bound, with both public bindings substituted. -/
theorem normalized_local {N : Nat} (answers : Fin N → Fin 2 → OracleAnswer)
    (seeds : Fin N → ProverCommitPublicBinding40.Private)
    (coins : Fin (N*n1 W Pr) → OracleAnswer) (k : Fin N) :
    attVec W Pr (ProverCommitGlobal42.normalized W Pr answers coins) k =
      vector W Pr (answers k 0) (answers k 1) (seeds k,attVec W Pr coins k) := by
  funext p
  rw [ProverCommitGlobal42.normalized_attVec]
  simp only [vector]
  cases hp : ProverCommitGlobal42.publicIndex W Pr p with
  | none => rfl
  | some b => fin_cases b <;> rfl

/-- Concrete gAddr at a private position agrees with the locally bounded
address, using the actual attVec coordinate map. -/
theorem global_private_address {N : Nat} (nonce : Fin N → NZ) (digest : OracleAnswer)
    (answers : Fin N → Fin 2 → OracleAnswer)
    (seeds : Fin N → ProverCommitPublicBinding40.Private)
    (coins : Fin (N*n1 W Pr) → OracleAnswer) (k : Fin N) (c : CPos Pr.E₁ Pr.E₂) :
    gAddr W Pr h B outputs x w
      (fun k => ProverCommitPublicBinding40.publicSec (nonce k) (seeds k)) digest
      (finProdFinEquiv (k,Pr.ord.symm (.inr c)))
      (ProverCommitGlobal42.normalized W Pr answers coins) =
    address W Pr h B outputs x w (nonce k) digest (answers k 0) (answers k 1)
      (seeds k,attVec W Pr coins k) c := by
  simp only [gAddr,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
  rw [normalized_local W Pr answers seeds coins k]
  rfl

#print axioms context_frozen_mass
#print axioms normalized_local
#print axioms global_private_address
end R1Z.ProverCommitContextBounds42
