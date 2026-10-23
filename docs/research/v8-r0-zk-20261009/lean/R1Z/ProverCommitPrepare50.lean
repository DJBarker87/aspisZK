import AspisR1ProducerRelease47.Dot50
import R1Z.ProverCommitNativeC49
import R1Z.ProverCommitReconstructModel49
import R1Z.ProverCommitChannelModel49
/-! Actual canonical component preparation, including both levels of additions.
No component/model identity is a hypothesis. -/
set_option autoImplicit false
namespace R1Z.ProverCommitPrepare50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisV8R15.ExactTowerBase
open AspisR1.ExtractedCurrentQM31Exact (decode)
open ProverCommitChannelAlgebra49 (cmComponents components)

def triple {A : Type} (x y z : A) : Nat → A := fun i => if i=0 then x else if i=1 then y else z

theorem triple_array {A : Type} (x y z : A) :
    Array.make 3#usize [x,y,z]=ProverCommitArray49.array 3#usize (triple x y z) := by
  rfl

theorem cm (x : Old.C) (hx : ProverCommitNativeC49.Canonical x) :
    ∃ a : Nat → U32,
      dot50.prepare_c (ProverCommitNativeC49.source x)=ok (ProverCommitArray49.array 3#usize a) ∧
      (∀ j, j<3 → (a j).val<AspisCircleGroupOrder.P) ∧
      (∀ j : Fin 3, ((a j.val).val : M31Exact)=cmComponents (ProverCommitNativeC49.value x) j) := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitM31Ops48.add_exact x.a x.b hx.1 hx.2
  refine ⟨triple x.a x.b z,?_,?_,?_⟩
  · simpa only [dot50.prepare_c,ProverCommitNativeC49.source,ProverCommitRelease47.convC,fromC,hz,bind_tc_ok] using
      congrArg Result.ok (triple_array x.a x.b z)
  · intro j hj
    unfold triple
    split <;> rename_i h
    · exact hx.1
    · split
      · exact hx.2
      · exact hcz
  · intro j
    fin_cases j
    · rfl
    · rfl
    · exact hdz

theorem q (x : Old.Q) (hx : Canonical x) :
    ∃ a : Nat → Nat → U32,
      dot50.prepare (ProverCommitNativeQ48.source x)=ok
        (ProverCommitArray49.array 3#usize (fun i => ProverCommitArray49.array 3#usize (a i))) ∧
      (∀ i j, i<3 → j<3 → (a i j).val<AspisCircleGroupOrder.P) ∧
      (∀ i j : Fin 3, ((a i.val j.val).val : M31Exact)=components (decode x) i j) := by
  obtain ⟨s,hs,hcs,hvs⟩ := ProverCommitNativeC49.add x.c0 x.c1 hx.1 hx.2
  obtain ⟨a,ha,hca,hva⟩ := cm x.c0 hx.1
  obtain ⟨b,hb,hcb,hvb⟩ := cm x.c1 hx.2
  obtain ⟨c,hc,hcc,hvc⟩ := cm s hcs
  refine ⟨triple a b c,?_,?_,?_⟩
  · change (do
      let z ← field.CM31.add (ProverCommitNativeC49.source x.c0) (ProverCommitNativeC49.source x.c1)
      let a ← dot50.prepare_c (ProverCommitNativeC49.source x.c0)
      let b ← dot50.prepare_c (ProverCommitNativeC49.source x.c1)
      let c ← dot50.prepare_c z
      ok (Array.make 3#usize [a,b,c]))=_
    rw [hs];simp only [bind_tc_ok,ha,hb,hc]
    exact congrArg Result.ok (triple_array _ _ _)
  · intro i j hi hj
    unfold triple
    split
    · exact hca j hj
    · split
      · exact hcb j hj
      · exact hcc j hj
  · intro i j
    fin_cases i
    · exact hva j
    · exact hvb j
    · change ((c j.val).val : M31Exact)=cmComponents
        (ProverCommitNativeC49.value x.c0+ProverCommitNativeC49.value x.c1) j
      exact (hvc j).trans (congrArg (fun z => cmComponents z j) hvs)


#print axioms triple_array
#print axioms cm
#print axioms q
end R1Z.ProverCommitPrepare50
