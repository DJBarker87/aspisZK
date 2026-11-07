import NMV_RslDomain
set_option autoImplicit false
namespace NMV_RslFold
open RSL NMV_RslLaws NMV_RslSnapshots NMV_RslDomain

/-- The full observation, including an abort/divergence prefix, at one child. -/
def observed {A B : Type} (child : A → Env → Obs B) (a : A) : Spec B :=
 fun env o => o=child a env

/-- Reach-sensitive substitution retains all three termination alternatives. -/
theorem bind_refine {A B : Type} (m : Spec A) (k l : A → Spec B) (env : Env)
 (step : ∀ a es, m env ⟨.ret a,es⟩ → ∀ o, k a env o → l a env o)
 (o : Obs B) (h : Spec.bind m k env o) : Spec.bind m l env o := by
 rcases h with ⟨a,e1,o2,hm,hk,ho⟩ | ⟨e1,hm,ho⟩ | ⟨e1,hm,ho⟩
 · exact Or.inl ⟨a,e1,o2,hm,step a e1 hm o2 hk,ho⟩
 · exact Or.inr (Or.inl ⟨e1,hm,ho⟩)
 · exact Or.inr (Or.inr ⟨e1,hm,ho⟩)

theorem bind_first {A B : Type} (m n : Spec A) (k : A → Spec B) (env : Env)
 (step : ∀ o, m env o → n env o) (o : Obs B)
 (h : Spec.bind m k env o) : Spec.bind n k env o := by
 rcases h with ⟨a,e1,o2,hm,hk,ho⟩ | ⟨e1,hm,ho⟩ | ⟨e1,hm,ho⟩
 · exact Or.inl ⟨a,e1,o2,step _ hm,hk,ho⟩
 · exact Or.inr (Or.inl ⟨e1,step _ hm,ho⟩)
 · exact Or.inr (Or.inr ⟨e1,step _ hm,ho⟩)

/-- Native cut target, NOT an actual-function producer: full SDK state,
allocator branches, exact owned-child arguments and complete child Result. -/
def stage2 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (a : TX2_240.Args) (s : SdkState) : Spec (Except ProgramError Unit × SdkState) :=
 if TX2_240.badRoute a then Spec.pure (.error .invalidInstructionData,s) else
 Spec.bind (Spec.emit (.returnData [])) fun _ =>
 Spec.bind (TX2_240.snapAll a.accounts TX2_240.snapLens s) fun r =>
 Spec.bind (Spec.env Env.clock) fun c =>
 Spec.bind (Spec.emit (.clock c)) fun _ =>
 Spec.bind (observed child ⟨a.program_id,r.1,a.data,c⟩) fun res => Spec.pure (res,r.2)

/-- Full-strength parameterized 240 fold, for EVERY verifier library V.
A native producer of stage2 remains separately required for a row root. -/
theorem fold240 (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D V child)
 (a : TX2_240.Args) (s : SdkState) (env : Env) (dom : TX2_240.Domain V a s)
 (o : Obs (Except ProgramError Unit × SdkState)) (h : stage2 child a s env o) :
 TX2_240.Ref L D V a s env o := by
 unfold stage2 at h
 unfold TX2_240.Ref
 split at h
 next bad => simp only [bad,if_true]; exact h
 next good =>
   simp only [good,if_false]
   have h7 : a.accounts.length=7 := by
     by_cases hh : a.accounts.length=7
     · exact hh
     · simp [TX2_240.badRoute,hh] at good
   apply bind_refine _ _ _ env ?_ o h
   intro _ _ _ o1 h1
   apply bind_refine _ _ _ env ?_ o1 h1
   intro r es hr o2 h2
   have facts := snapAll_facts a.accounts TX2_240.snapLens s r.2 r.1 env es hr
   apply bind_refine _ _ _ env ?_ o2 h2
   intro c _ _ o3 h3
   apply bind_refine _ _ _ env ?_ o3 h3
   intro _ _ _ o4 h4
   apply bind_first _ _ _ env ?_ o4 h4
   intro oc hc
   change oc=child _ env at hc
   subst oc
   have hd := domain241 V a s r.1 c h7 facts.2 dom
   exact ⟨hd,packet _ env hd⟩

/-- Full 344 cut target. The copy retains borrow failure, length panic,
write event and exclusive-guard release in exactly the canonical relation. -/
def stage1 (child : TX1_345.Args → Env → Obs (Except ProgramError Bytes))
 (a : TX1_344.Args) (s : SdkState) : Spec (Except ProgramError Unit × SdkState) :=
 if TX1_344.badRoute a then Spec.pure (.error .invalidInstructionData,s) else
 Spec.bind (TX2_240.snapAll a.accounts TX1_344.snapLens s) fun r =>
 Spec.bind (observed child ⟨a.program_id,r.1,a.data⟩) fun res =>
 match res with
 | .error e => Spec.pure (.error e,r.2)
 | .ok ck => match a.accounts[2]? with
   | none => Spec.panic
   | some acc2 => TX1_344.copyStep acc2 ck r.2

theorem fold344 (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (child : TX1_345.Args → Env → Obs (Except ProgramError Bytes))
 (packet : TX1_345.RowSpec_345 V P C child)
 (a : TX1_344.Args) (s : SdkState) (env : Env)
 (o : Obs (Except ProgramError Unit × SdkState)) (h : stage1 child a s env o) :
 TX1_344.Ref V P C a s env o := by
 unfold stage1 at h
 unfold TX1_344.Ref
 split at h
 next bad => simp only [bad,if_true]; exact h
 next good =>
   simp only [good,if_false]
   apply bind_refine _ _ _ env ?_ o h
   intro r _ _ oc hc
   apply bind_first _ _ _ env ?_ oc hc
   intro oo ho
   change oo=child _ env at ho
   subst oo
   exact ⟨trivial,packet _ env trivial⟩

#print axioms bind_refine
#print axioms bind_first
#print axioms fold240
#print axioms fold344
end NMV_RslFold
