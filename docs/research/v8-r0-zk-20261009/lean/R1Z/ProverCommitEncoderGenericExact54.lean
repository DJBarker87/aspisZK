import AspisR1ProducerRelease47.EncoderGenericAt54
import R1Z.ProverCommitEncoderGenericModel54
/-! Both complete generic entry points, with all node/point/channel images
derived. Only the explicit local scalar-operation laws remain generic. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEncoderGenericExact54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitArray49 ProverCommitEncoderEval54 ProverCommitEncoderGenericEval54
open ProverCommitEncoderGenericModel54 AspisCircleGroupOrder
variable {E K : Type} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod P) K]
attribute [local irreducible] array ProverCommitEncoderMath54.evaluate

theorem encode_result (inst : scalar.CodeField E) (valid : E → Prop) (decode : E → K)
    (nv : U32 → K) (ops : Arithmetic inst valid decode nv)
    (sub_success : ∀ x y, valid x → valid y → ∃ z, inst.sub x y=ok z ∧ valid z ∧ decode z=decode x-decode y)
    (hnv : ∀ m : U32, m.val<2147483647 → nv m=algebraMap (ZMod P) K (ProverCommitM31Ops48.decode m))
    (f : Nat → E) (hf : ∀ i, i<1024 → valid (f i))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ out : Nat → E, generic54.encode_at inst (array 1024#usize f) j=ok (array 4#usize out) ∧
      (∀ s, s<4 → valid (out s)) ∧
      ∀ s : Fin 4, decode (out s.val)=AspisWide.InitialEncoder.exactInitialEncoder
        (fun i => decode (f i.val)) (AspisV5ComponentCConcreteFoldLinearity.childIndex u s) := by
  obtain ⟨p,hp,hcp,hdp⟩ := node_image nv hnv j u hj
  obtain ⟨c,x,y,hc,hx,hy,hcx,hcy,hdx,hdy⟩ := point_image inst valid decode nv ops hnv j u hj
  obtain ⟨out,hout,hcout,hdout⟩ := ProverCommitEncoderGenericLeaf54.exact_result inst valid decode nv ops
    sub_success f hf p hcp x y hcx hcy
  refine ⟨out,?_,hcout,?_⟩
  · rw [generic54.encode_at,hc]
    simp only [bind_tc_ok,hp,hx,hy]
    exact hout
  · intro s
    rw [hdout s,hdx,hdy]
    let q : Fin 1024 → K := fun i => decode (f i.val)
    have he : (fun s : Fin 4 => ProverCommitEncoderMath54.evaluate 8 (fun i => decode (f (4*i+s.val)))
        (fun i => nv (p i)) 0)=
        (fun s => AspisWide.FinalEncoder.exactFinalEncoder
          (AspisV5FriConcreteEncoderCommutation.coefficientLane 256 s q) u) := by
      funext s
      rw [recurrence_value (fun i => decode (f (4*i+s.val))) nv p u (by intro k hk;exact hdp k (by omega))]
      rfl
    rw [he,ProverCommitEncoderPhiModel53.phi_fibre]
    exact (congrFun (AspisR1.FirstFold.encoded_fibre q u) s).symm

theorem eval_result (inst : scalar.CodeField E) (valid : E → Prop) (decode : E → K)
    (nv : U32 → K) (ops : Arithmetic inst valid decode nv)
    (hnv : ∀ m : U32, m.val<2147483647 → nv m=algebraMap (ZMod P) K (ProverCommitM31Ops48.decode m))
    (f : Nat → E) (hf : ∀ i, i<256 → valid (f i))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ z : E, generic54.eval_at inst (Array.to_slice (array 256#usize f)) j 8#usize=ok z ∧
      valid z ∧ decode z=AspisWide.FinalEncoder.exactFinalEncoder (fun i => decode (f i.val)) u := by
  obtain ⟨p,hp,hcp,hdp⟩ := node_image nv hnv j u hj
  have hlist : (Array.to_slice (array 256#usize f)).val=List.ofFn (fun i : Fin (2^8) => f i.val) := by
    have hs : (256#usize).val=2^8 := rfl
    change (array 256#usize f).val=_
    simp only [array,hs,Fin.val_cast]
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitEncoderGenericEval54.exact_result inst valid decode nv ops
    8 (by decide) 8#usize 0#usize rfl (by decide) f hf (Array.to_slice (array 256#usize f)) hlist p hcp
  refine ⟨z,?_,hcz,?_⟩
  · rw [generic54.eval_at,hp]
    exact hz
  · rw [hdz,show (0#usize).val=0 from rfl,recurrence_value (fun i => decode (f i)) nv p u
      (by intro k hk;exact hdp k (by omega))]

#print axioms encode_result
#print axioms eval_result
end R1Z.ProverCommitEncoderGenericExact54
