import R1Z.ProverCommitEncoderGenericLeaf54
import R1Z.ProverCommitEncoderGeometry54
import R1Z.ProverCommitEncoderNodes54
import R1Z.ProverCommitEncoderLift54
import R1Z.ProverCommitEncoderPhiModel53
/-! Generic mathematical bridge, with native scalar operation premises explicit. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEncoderGenericModel54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitEncoderEval54 ProverCommitEncoderGenericEval54
open ProverCommitEncoderMath54 AspisCircleTensorBinding AspisCircleGroupOrder
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod P) K]

attribute [local irreducible] ProverCommitEncoderMath54.evaluate doubledFactor naturalLineValue

theorem recurrence_value (f : Nat → K) (nv : U32 → K) (p : Nat → U32) (u : Fin 262144)
    (hp : ∀ k, k<8 → nv (p k)=doubledFactor
      (algebraMap (ZMod P) K (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)) k) :
    ProverCommitEncoderMath54.evaluate 8 f (fun i => nv (p i)) 0=
      AspisWide.FinalEncoder.exactFinalEncoder (fun i => f i.val) u := by
  rw [nodes_congr 8 f (fun i => nv (p i))
    (doubledFactor (algebraMap (ZMod P) K (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)))
    0 (by intro k hk;simpa only [Nat.zero_add] using hp k hk),evaluate_natural,doubledFactor]
  rw [AspisWide.FinalEncoder.exactFinalEncoder,AspisWide.FinalEncoder.exactFinalLinear_apply,
    AspisV5FriConcreteEncoderApplicability.naturalCoefficientPolynomial_eval_eq_sum (by decide)]
  exact (Fin.sum_univ_eq_sum_range (fun i => f i*naturalLineValue
    (algebraMap (ZMod P) K (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)) i) 256).symm

theorem node_image (nv : U32 → K)
    (hnv : ∀ m : U32, m.val<2147483647 → nv m=algebraMap (ZMod P) K (ProverCommitM31Ops48.decode m))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ p : Nat → U32, nodes54.nodes j=ok (nodes p) ∧
      (∀ i, i<9 → (p i).val<2147483647) ∧
      ∀ i, i<9 → nv (p i)=doubledFactor
        (algebraMap (ZMod P) K (AspisV7ExactOneFoldDomains.storedFirstLineX18 u)) i := by
  obtain ⟨p,hp,hcp,hdp⟩ := ProverCommitEncoderNodes54.exact_result j (by rw [hj];exact u.isLt)
  refine ⟨p,hp,hcp,?_⟩
  intro i hi
  rw [hnv _ (hcp i hi),hdp i hi,hj,ProverCommitEncoderGeometry54.node_value u i (by omega),
    ProverCommitEncoderLift54.map_doubled]

theorem point_image {E : Type} (inst : scalar.CodeField E) (valid : E → Prop)
    (decode : E → K) (nv : U32 → K) (ops : Arithmetic inst valid decode nv)
    (hnv : ∀ m : U32, m.val<2147483647 → nv m=algebraMap (ZMod P) K (ProverCommitM31Ops48.decode m))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ c x y, nodes54.point j=ok (ProverCommitNativeC49.source c) ∧
      inst.from_m31 (ProverCommitNativeC49.source c).a=ok x ∧
      inst.from_m31 (ProverCommitNativeC49.source c).b=ok y ∧ valid x ∧ valid y ∧
      decode x=AspisWide.FinalEncoder.exactCircleX u ∧ decode y=AspisWide.FinalEncoder.exactCircleY u := by
  obtain ⟨c,hc,hcc,hdc⟩ := ProverCommitEncoderCircle54.point_model j u hj
  obtain ⟨x,hx,hcx,hdx⟩ := ops.from_success c.a hcc.1
  obtain ⟨y,hy,hcy,hdy⟩ := ops.from_success c.b hcc.2
  refine ⟨c,x,y,hc,hx,hy,hcx,hcy,?_,?_⟩
  · have hre := congrArg (fun z : AspisV8R15.ExactTowerBase.CM31Exact => z.re) hdc
    have he : ProverCommitM31Ops48.decode c.a=X (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 u) := hre
    rw [hdx,hnv _ hcc.1,he]
    rfl
  · have him := congrArg (fun z : AspisV8R15.ExactTowerBase.CM31Exact => z.im) hdc
    have he : ProverCommitM31Ops48.decode c.b=(AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 u).1.2 := him
    rw [hdy,hnv _ hcc.2,he]
    rfl

#print axioms recurrence_value
#print axioms node_image
#print axioms point_image
end R1Z.ProverCommitEncoderGenericModel54
