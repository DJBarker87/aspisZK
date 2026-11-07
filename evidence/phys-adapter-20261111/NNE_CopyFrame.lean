import NNE_AcceptedCuts
import NNE_SdkRelease
set_option autoImplicit false
namespace NNE_CopyFrame
open RSL NMV_RslLaws
/-- Exact returned write footprint. The proof inverts the exclusive acquisition,
length gate, write and guard release in the SAME copyStep observation. -/
theorem copy_ok (a : AccountInfo) (ck : Bytes) (s post : SdkState) (env : Env)
 (es : List Event) (h : TX1_344.copyStep a ck s env ⟨.ret (.ok (),post),es⟩) :
 (∀ i, (post.cells i).payload = if i = a.cell then ck else (s.cells i).payload) ∧
 ck.length = (payload a s).length ∧
 ∃ token es1 es2,
  es = es1 ++ (.write a.cell ck :: es2) ∧
  es1 = [.acquire a.cell token .exclusive true] ∧
  es2 = [.release a.cell token .exclusive] := by
 unfold TX1_344.copyStep at h
 obtain ⟨⟨r,s2⟩,es1,esx,ha,hk,he⟩ := bind_return _ _ _ _ _ h
 have f := acquire_frame a .exclusive s s2 r env es1 ha
 cases r with
 | error error => simp [Spec.pure] at hk
 | ok token =>
  split at hk
  next mismatch => simp [Spec.panic] at hk
  next lengths =>
   obtain ⟨_,_,_,hw,hk,he2⟩ := bind_return _ _ _ _ _ hk
   simp only [Spec.emit,Obs.mk.injEq] at hw
   rcases hw with ⟨_,rfl⟩
   obtain ⟨s4,es2,_,hr,hp,he3⟩ := bind_return _ _ _ _ _ hk
   have g := release_frame a token .exclusive
     (s2.put a.cell {(s2.cells a.cell) with payload := ck}) s4 env es2 hr
   simp only [Spec.pure,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hp
   rcases hp with ⟨⟨_,rfl⟩,rfl⟩
   refine ⟨?_,?_,token,es1,es2,?_,?_,?_⟩
   · intro i
     rw [g i]
     by_cases hi : i = a.cell
     · subst i; simp [SdkState.put]
     · simp [SdkState.put,hi,f i]
   · have hl : ck.length = (payload a s2).length := by simpa only [bne_iff_ne,not_not] using lengths
     exact hl.trans (congrArg List.length (f a.cell))
   · simp only [he,he2,he3,List.cons_append,List.nil_append,List.append_nil]
   · have hh := (NNE_SdkAcquire.relation s a .exclusive env _).mp ha
     by_cases hb : NNE_SdkAcquire.allowed s a .exclusive = true
     · simp only [NNE_SdkAcquire.reply,hb,if_true,Obs.mk.injEq,Exit.ret.injEq,Prod.mk.injEq] at hh
       rcases hh with ⟨⟨ht,_⟩,hev⟩
       cases ht
       exact hev
     · simp [NNE_SdkAcquire.reply,hb] at hh
   · have hh := (NNE_SdkRelease.relation _ a token .exclusive env _).mp hr
     exact congrArg Obs.events hh

#print axioms copy_ok
end NNE_CopyFrame
