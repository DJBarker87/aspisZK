import NMV_RslFold
set_option autoImplicit false
namespace NNE_RslOk
open RSL NMV_RslLaws
/-- The SAME accepted344 observation exposes its actual ordered cuts. No
successful child or endpoint is a premise: those follow from the full RowSpec. -/
theorem first_ok (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (a : TX1_344.Args) (s post : SdkState) (env : Env) (es : List Event)
 (h : TX1_344.Ref V P C a s env ⟨.ret (.ok (),post),es⟩) :
 ∃ xs mid ck acc2 es1 es2 es3,
  TX1_344.badRoute a = false ∧
  TX2_240.snapAll a.accounts TX1_344.snapLens s env ⟨.ret (xs,mid),es1⟩ ∧
  TX1_345.Ref V P C ⟨a.program_id,xs,a.data⟩ env ⟨.ret (.ok ck),es2⟩ ∧
  a.accounts[2]? = some acc2 ∧
  TX1_344.copyStep acc2 ck mid env ⟨.ret (.ok (),post),es3⟩ ∧
  es = es1 ++ (es2 ++ es3) := by
 unfold TX1_344.Ref at h
 split at h
 next bad => simp [Spec.pure] at h
 next good =>
  obtain ⟨⟨xs,mid⟩,es1,tail,hs,hk,he⟩ := bind_return _ _ _ _ _ h
  obtain ⟨r,es2,es3,hc,hw,he2⟩ := bind_return _ _ _ _ _ hk
  cases r with
  | error e => simp [Spec.pure] at hw
  | ok ck =>
   cases hi : a.accounts[2]? with
   | none => simp [hi,Spec.panic] at hw
   | some acc2 =>
    simp only [hi] at hw
    exact ⟨xs,mid,ck,acc2,es1,es2,es3,Bool.eq_false_iff.mpr good,
      hs,hc.2,rfl,hw,by rw [he,he2]⟩

/-- The SAME accepted240 observation includes the Clock reply at the child
call. Slot association is still RuntimeClockSlotBinding, not a guessed value. -/
theorem second_ok (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (a : TX2_240.Args) (s post : SdkState) (env : Env) (es : List Event)
 (h : TX2_240.Ref L D V a s env ⟨.ret (.ok (),post),es⟩) :
 ∃ xs es1 es2,
  TX2_240.badRoute a = false ∧
  TX2_240.snapAll a.accounts TX2_240.snapLens s env ⟨.ret (xs,post),es1⟩ ∧
  TX2_241.Domain V ⟨a.program_id,xs,a.data,env.clock⟩ ∧
  TX2_241.Ref L D V ⟨a.program_id,xs,a.data,env.clock⟩ env ⟨.ret (.ok ()),es2⟩ ∧
  es = .returnData [] :: (es1 ++ (.clock env.clock :: es2)) := by
 unfold TX2_240.Ref at h
 split at h
 next bad => simp [Spec.pure] at h
 next good =>
  obtain ⟨_,_,_,hemit,hk,he⟩ := bind_return _ _ _ _ _ h
  simp only [Spec.emit,Obs.mk.injEq] at hemit
  rcases hemit with ⟨_,rfl⟩
  obtain ⟨⟨xs,mid⟩,es1,tail,hs,hk,he2⟩ := bind_return _ _ _ _ _ hk
  obtain ⟨clock,_,_,hc,hk,he3⟩ := bind_return _ _ _ _ _ hk
  simp only [Spec.env,Obs.mk.injEq,Exit.ret.injEq] at hc
  rcases hc with ⟨rfl,rfl⟩
  obtain ⟨_,_,_,hemit,hk,he4⟩ := bind_return _ _ _ _ _ hk
  simp only [Spec.emit,Obs.mk.injEq] at hemit
  rcases hemit with ⟨_,rfl⟩
  obtain ⟨r,es2,_,hc,hp,he5⟩ := bind_return _ _ _ _ _ hk
  simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hp
  rcases hp with ⟨⟨rfl,rfl⟩,rfl⟩
  refine ⟨xs,es1,es2,Bool.eq_false_iff.mpr good,hs,hc.1,hc.2,?_⟩
  simp only [he,he2,he3,he4,he5,List.nil_append,List.append_nil,List.cons_append]

#print axioms first_ok
#print axioms second_ok
end NNE_RslOk
