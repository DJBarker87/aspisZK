import NNE_PhysicalAccepted
set_option autoImplicit false
namespace NNE_RslError
open RSL NMV_RslLaws

theorem copy_error (e : AspisR1.S2W_D189Entry.Entry) (n : Nat) (ck : Bytes)
 (env : Env) (error : ProgramError) (post : SdkState) (es : List Event) :
 ¬ TX1_344.copyStep (NNE_Entry.account e 2) ck (NNE_Entry.state e n) env
   ⟨.ret (.error error,post),es⟩ := by
 intro h
 unfold TX1_344.copyStep at h
 obtain ⟨⟨r,s2⟩,es1,tail,ha,hk,_⟩ := bind_return _ _ _ _ _ h
 have ha' := (NNE_SdkAcquire.relation _ _ .exclusive env _).mp ha
 simp only [NNE_SdkAcquire.reply,NNE_SdkAcquire.next,NNE_SdkAcquire.allowed,
  exclusiveOk,NNE_Entry.state,Option.isNone_none,List.isEmpty_nil,Bool.and_self,
  if_true,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at ha'
 rcases ha' with ⟨⟨rfl,rfl⟩,_⟩
 dsimp only at hk
 split at hk
 next bad => simp [Spec.panic] at hk
 next good =>
  obtain ⟨_,_,_,_,hk,_⟩ := bind_return _ _ _ _ _ hk
  obtain ⟨_,_,_,_,hp,_⟩ := bind_return _ _ _ _ _ hk
  simp [Spec.pure] at hp

theorem first (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (err : NNE_Snapshot.PE → ProgramError) (invalid : err .InvalidAccountData = .invalidAccountData)
 (e : AspisR1.S2W_D189Entry.Entry) (p : AspisR1.S2W_ExtractionBoundary.Program)
 (data : Aeneas.Std.Slice Aeneas.Std.U8) (env : Env)
 (post : SdkState) (error : ProgramError) (es : List Event)
 (route : AspisR1.Hiq_ReleaseRoute.stage1 data)
 (h : TX1_344.Ref V P C (NNE_EntryArgs.args e 3 p data) (NNE_Entry.state e 0) env
   ⟨.ret (.error error,post),es⟩) :
 ∃ es', TX1_345.Ref V P C (NNE_PhysicalAccepted.child1 err e p data) env
  ⟨.ret (.error error),es'⟩ := by
 unfold TX1_344.Ref at h
 split at h
 next bad =>
  have hg := NNE_EntryArgs.first_guard e p data route
  simp [hg] at bad
 next good =>
  obtain ⟨⟨xs,mid⟩,es1,_,hs,hk,_⟩ := bind_return _ _ _ _ _ h
  obtain ⟨hxs,hmid⟩ := NNE_SnapshotSequence.first err invalid e 0 env xs mid es1 hs
  subst xs; subst mid
  obtain ⟨r,es2,_,hc,hw,_⟩ := bind_return _ _ _ _ _ hk
  cases r with
  | error pe =>
   simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq,Except.error.injEq] at hw
   rcases hw with ⟨⟨rfl,_⟩,_⟩
   exact ⟨es2,hc.2⟩
  | ok ck =>
   have ha : (NNE_EntryArgs.args e 3 p data).accounts[2]? = some (NNE_Entry.account e 2) := by
    simp [NNE_EntryArgs.args]
   simp only [ha] at hw
   exact False.elim (copy_error e 3 ck env error post _ hw)
#print axioms copy_error
#print axioms first
end NNE_RslError
