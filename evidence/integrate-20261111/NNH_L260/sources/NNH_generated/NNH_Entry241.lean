import NNH_Libraries
import NNH_InstalledImpl
import NNH_RSLReads
set_option autoImplicit false
noncomputable section
namespace NNH_Entry241
open RSL NNH_Libraries NMV_RslLaws

theorem entry_asq8 (I0 : TAS.Impl L V0 VL)
 (a1 a2 : NMV_ConcreteWindows.Allocation) (a : TX2_240.Args) (s : SdkState) (env : Env)
 (route : TAS.ASQ8 a.data) :
 (NNH_InstalledImpl.install I0 a1 a2).entry a s env =
 NMV_ConcreteWindows.stage2 a2 I0.f241 a s env := by
 change NNF_Dispatch.entry (NNF_Dispatch.process _ _) a s env = _
 simp only [NNF_Dispatch.entry,NNF_Dispatch.process,TAS.asq8_admitted route,
  TAS.asq8_not_stage1 route,Bool.false_eq_true,if_true,if_false]
 rfl

/-- The actual installed entry's accepted execution produces the SAME actual
241 call and its owned snapshot arguments. No successful child is assumed. -/
theorem actual (I0 : TAS.Impl L V0 VL)
 (a1 a2 : NMV_ConcreteWindows.Allocation) (a : TX2_240.Args) (s post : SdkState) (env : Env)
 (route : TAS.ASQ8 a.data)
 (accepted : ((NNH_InstalledImpl.install I0 a1 a2).entry a s env).exit=.ret (.ok (),post)) :
 ∃ xs : List OwnedAccount,
 (∀ x∈xs, TX2_241.Consistent x) ∧
 (I0.f241 ⟨a.program_id,xs,a.data,env.clock⟩ env).exit=.ret (.ok ()) := by
 rw [entry_asq8 I0 a1 a2 a s env route] at accepted
 have run := NMV_WindowStage.cut240 (NMV_ConcreteWindows.windows (a2 a s env)) I0.f241 a s env
 change NMV_RslFold.stage2 I0.f241 a s env (NMV_ConcreteWindows.stage2 a2 I0.f241 a s env) at run
 have shape : NMV_ConcreteWindows.stage2 a2 I0.f241 a s env =
   ⟨.ret (.ok (),post),(NMV_ConcreteWindows.stage2 a2 I0.f241 a s env).events⟩ := by
  cases h : NMV_ConcreteWindows.stage2 a2 I0.f241 a s env
  simp only [Obs.mk.injEq]
  exact ⟨by simpa only [h] using accepted,trivial⟩
 rw [shape] at run
 unfold NMV_RslFold.stage2 at run
 split at run
 · cases congrArg Obs.exit run
 · obtain ⟨_,_,_,_,h,_⟩ := bind_return _ _ _ _ _ run
   obtain ⟨r,es,_,snap,h,_⟩ := bind_return _ _ _ _ _ h
   have images := (NMV_RslSnapshots.snapAll_facts _ _ _ _ _ _ _ snap).2
   obtain ⟨clock,_,_,clockLaw,h,_⟩ := bind_return _ _ _ _ _ h
   change (⟨.ret clock,_⟩ : Obs (Except ProgramError UInt64)) = ⟨.ret env.clock,[]⟩ at clockLaw
   have clockEq := congrArg Obs.exit clockLaw
   have sameClock : clock=env.clock := Exit.ret.inj clockEq
   subst clock
   obtain ⟨_,_,_,_,h,_⟩ := bind_return _ _ _ _ _ h
   obtain ⟨res,_,_,observed,pureLaw,_⟩ := bind_return _ _ _ _ _ h
   change _ = I0.f241 _ env at observed
   have result := congrArg Obs.exit pureLaw
   change Exit.ret (.ok (),post) = Exit.ret (res,r.2) at result
   have resultEq := (Prod.mk.inj (Exit.ret.inj result)).1
   refine ⟨r.1,NMV_RslSnapshots.images_consistent s _ _ _ images,?_⟩
   rw [←observed]
   exact congrArg Exit.ret resultEq.symm

/-- Weak241 producer from actual entry acceptance, using the canonical
library-parametric row field. No Root0, accepted2, model2 or free selector. -/
theorem weak (I0 : TAS.Impl L V0 VL)
 (a1 a2 : NMV_ConcreteWindows.Allocation)
 (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
 (row : TX2_241.RowSpec_241 L D (TCK.weaken V0 w) I0.f241)
 (a : TX2_240.Args) (s post : SdkState) (env : Env) (route : TAS.ASQ8 a.data)
 (accepted : ((NNH_InstalledImpl.install I0 a1 a2).entry a s env).exit=.ret (.ok (),post)) :
 ∃ xs : List OwnedAccount, ∃ es : List Event,
 I0.f241 ⟨a.program_id,xs,a.data,env.clock⟩ env=⟨.ret (.ok ()),es⟩ ∧
 TX2_241.Ref L D (TCK.weaken V0 w) ⟨a.program_id,xs,a.data,env.clock⟩ env ⟨.ret (.ok ()),es⟩ := by
 obtain ⟨xs,consistent,ok⟩ := actual I0 a1 a2 a s post env route accepted
 have law := row ⟨a.program_id,xs,a.data,env.clock⟩ env (TCK.domain241_weaken V0 w _ consistent)
 have shape : I0.f241 ⟨a.program_id,xs,a.data,env.clock⟩ env =
   ⟨.ret (.ok ()),(I0.f241 ⟨a.program_id,xs,a.data,env.clock⟩ env).events⟩ := by
  cases h : I0.f241 ⟨a.program_id,xs,a.data,env.clock⟩ env
  simp only [Obs.mk.injEq]
  exact ⟨by simpa only [h] using ok,trivial⟩
 exact ⟨xs,_,shape,shape ▸ law⟩

#print axioms entry_asq8
#print axioms actual
#print axioms weak
end NNH_Entry241
