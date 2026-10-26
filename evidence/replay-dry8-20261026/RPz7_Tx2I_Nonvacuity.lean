import RPz7_Tx2I_Accepted
import RPz7_Op3I_Witness
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2I_Nonvacuity
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
attribute [local instance] Classical.propDecidable

/-- D188 consistency for the specialized dictionary, for arbitrary remaining
operations. No native deployment or joint cryptographic admissibility claim. -/
theorem extraction_satisfiable {W : Type} (adapter : AdapterRw.Ops)
    (current : AspisR1CurrentCaller.Ops) (base : VTop_Stages.Ops) (finish : FinishOps W)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) :
    ∃ native1 native2,
      S2W_DigestExtraction.AeneasExtraction
        (ClaimsUnrolledSdk.sdkOps
          (Tx2I_Install.install {adapter with op43 := S2W_DigestExtraction.digest hashv} base finish)
          (Op3I_Install.install current) B std) native1 native2 hashv := by
  let actual := ClaimsUnrolledSdk.sdkOps
    (Tx2I_Install.install {adapter with op43 := S2W_DigestExtraction.digest hashv} base finish)
    (Op3I_Install.install current) B std
  exact ⟨AdapterRw.r1_pool_adapter.owned.stage1_owned actual,
    AdapterRw.r1_pool_adapter.owned.stage2_owned actual,
    ⟨by intros; rfl,by intros; rfl,by intros; rfl⟩⟩

theorem shape_success : Tx2I_Install.shape Op3I_Witness.proof = ok (.Ok .S2) := by
  have source := Op3I_Witness.source_success
  unfold Op3I_Install.sourceBody at source
  obtain ⟨r,call,rest⟩ := Op3I_ParseLaws.bind_success _ _ _ source
  cases r with
  | Err e => cases rest
  | Ok raw =>
    obtain ⟨rfl,_⟩ := Op3I_ParseLaws.source_success _ raw call
    simp only [Tx2I_Install.shape,call,bind_tc_ok,Tx2I_Install.variant]

/-- A local consistency interpretation of the still-explicit primitive leaves.
It is not the production arithmetic implementation. -/
def leaves (x : E) : FinishOps Unit where
  field := fun _ _ => ok x
  quarter := ok 0#u32
  add := fun _ _ => ok x
  mulM := fun _ _ => ok x
  ne := fun _ _ => ok false
  polynomial := fun _ _ => ok x
  trace := fun _ _ _ => ok ()
  folds := fun _ => ok 2#usize
  newWeights := fun _ _ _ => ok (.Ok ())
  pair := fun _ _ _ _ => ok (.Ok x)
  mark := fun _ _ => ok ()
  dot := fun _ _ => ok (.Ok x)

/-- The source finish installation can succeed; no finish-success premise. -/
theorem finish_success (x : E) (p0 : verifier.Prepared)
    (a0 : verifier.Accumulator) (v : verifier.View) :
    Port4D_FinishInstall.finish (leaves x) v
      {p0 with variant := .S2, alpha := Array.repeat 2#usize x}
      {a0 with rhs := x, next := 22#usize} none = ok (.Ok ()) := by
  let p : verifier.Prepared := {p0 with variant := .S2, alpha := Array.repeat 2#usize x}
  let a : verifier.Accumulator := {a0 with rhs := x, next := 22#usize}
  let r (bytes : Slice U8) (alpha claim : E) : RowFinish_Control.RoundValues (leaves x) bytes alpha claim :=
    ⟨x,x,x,0#u32,x,x,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have value := RowFinish_Control.parent_value (leaves x) v p a x x
    (r v.round0 x p.claim) (r v.round1 x x) () (Array.repeat 2#usize x).to_slice x x
    rfl (by rfl) (by rfl) rfl (by rfl) rfl rfl
  have success : Port3_NativeFinishBody.verifier.finish_relation
      (Port4D_Round.native (leaves x)) v p a none = ok (.Ok ()) := by
    simpa only [r,a,ne_eq,not_true_eq_false,if_false,bne_self_eq_false] using value
  exact (Port3_QueryInstall.success_iff _ ()).mpr success

#print axioms extraction_satisfiable
#print axioms shape_success
#print axioms finish_success
end AspisR1.Tx2I_Nonvacuity
end
