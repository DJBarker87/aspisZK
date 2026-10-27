import FJg_ReadKCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_ReadSemanticCanon
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish

theorem source (bytes : Slice U8) (start stop : Usize) (alpha : Array K 10#usize)
    (run : CheckpointBytes4Ops.readSemanticAlpha bytes start=ok (.Ok (alpha,stop))) :
    FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) := by
  unfold CheckpointBytes4Ops.readSemanticAlpha CheckpointBytes4Ops.semanticUsing at run
  obtain ⟨q0,r0,h0,c0,run⟩ := FJg_ReadKCut.reached _ _ _ run
  obtain ⟨q1,r1,h1,c1,run⟩ := FJg_ReadKCut.reached _ _ _ run
  obtain ⟨q2,r2,h2,c2,run⟩ := FJg_ReadKCut.reached _ _ _ run
  obtain ⟨q3,r3,h3,c3,run⟩ := FJg_ReadKCut.reached _ _ _ run
  obtain ⟨q4,r4,h4,c4,run⟩ := FJg_ReadKCut.reached _ _ _ run
  obtain ⟨q5,r5,h5,c5,run⟩ := FJg_ReadKCut.reached _ _ _ run
  obtain ⟨q6,r6,h6,c6,run⟩ := FJg_ReadKCut.reached _ _ _ run
  obtain ⟨q7,r7,h7,c7,run⟩ := FJg_ReadKCut.reached _ _ _ run
  obtain ⟨q8,r8,h8,c8,run⟩ := FJg_ReadKCut.reached _ _ _ run
  obtain ⟨q9,r9,h9,c9,run⟩ := FJg_ReadKCut.reached _ _ _ run
  cases Result.ok.inj run
  intro x hx
  change x∈[_,_,_,_,_,_,_,_,_,_] at hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals assumption

/-- Actual native semantic helper, same returned array, without caller canon. -/
theorem native (reserved : Bool) (bytes : Slice U8) (start stop : Usize) (alpha : Array K 10#usize)
    (run : (T2Nat_ReaderOps.ops reserved).readSemanticAlpha bytes start=ok (.Ok (alpha,stop))) :
    FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) := by
  exact source bytes start stop alpha ((T2Nat_ReaderOps.semantic reserved bytes start (.Ok (alpha,stop))).mp run)
#print axioms source
#print axioms native
end AspisR1.FJg_ReadSemanticCanon
end
