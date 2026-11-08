import RSL_TX1_344
set_option autoImplicit false
namespace NMV_RslLaws
open RSL

/-- Account bytes only; the full SDK state remains an explicit argument. -/
def PayloadFrame (s t : SdkState) : Prop := ∀ i, (t.cells i).payload = (s.cells i).payload

theorem frame_refl (s : SdkState) : PayloadFrame s s := fun _ => rfl

theorem frame_trans {s t u : SdkState} (h : PayloadFrame s t) (k : PayloadFrame t u) :
    PayloadFrame s u := fun i => (k i).trans (h i)

theorem bind_return {α β : Type} (m : Spec α) (k : α → Spec β) (env : Env)
    (b : β) (es : List Event) (h : Spec.bind m k env ⟨.ret b, es⟩) :
    ∃ a e1 e2, m env ⟨.ret a,e1⟩ ∧ k a env ⟨.ret b,e2⟩ ∧ es=e1++e2 := by
  rcases h with ⟨a,e1,o2,hm,hk,ho⟩ | ⟨e1,_,ho⟩ | ⟨e1,_,ho⟩
  · cases o2 with | mk ex ev =>
    have hh := congrArg Obs.exit ho
    simp only at hh
    cases hh
    exact ⟨a,e1,ev,hm,hk,congrArg Obs.events ho⟩
  · cases congrArg Obs.exit ho
  · cases congrArg Obs.exit ho

theorem emit_return {α : Type} (ev : Event) (k : Unit → Spec α) (env : Env)
    (a : α) (es : List Event) (h : Spec.bind (Spec.emit ev) k env ⟨.ret a,es⟩) :
    ∃ tail, k () env ⟨.ret a,tail⟩ ∧ es=ev::tail := by
  obtain ⟨u,e1,e2,hm,hk,he⟩ := bind_return _ _ _ _ _ h
  simp only [Spec.emit, Obs.mk.injEq, Exit.ret.injEq] at hm
  rcases hm with ⟨_,rfl⟩
  cases u
  exact ⟨e2,hk,he⟩

theorem acquire_frame (a : AccountInfo) (k : Kind) (s t : SdkState)
    (r : Except ProgramError Nat) (env : Env) (es : List Event)
    (h : acquire a k s env ⟨.ret (r,t),es⟩) : PayloadFrame s t := by
  unfold acquire at h
  cases k <;> (simp only at h; split at h)
  all_goals
    obtain ⟨tail,hp,_⟩ := emit_return _ _ _ _ _ h
    simp only [Spec.pure, Obs.mk.injEq, Exit.ret.injEq, Prod.mk.injEq] at hp
    rcases hp with ⟨⟨_,rfl⟩,_⟩
    intro i
    by_cases hi : i=a.cell <;> simp [SdkState.put,hi]

theorem release_frame (a : AccountInfo) (token : Nat) (k : Kind)
    (s t : SdkState) (env : Env) (es : List Event)
    (h : release a token k s env ⟨.ret t,es⟩) : PayloadFrame s t := by
  unfold release at h
  obtain ⟨tail,hp,_⟩ := emit_return _ _ _ _ _ h
  simp only [Spec.pure, Obs.mk.injEq, Exit.ret.injEq] at hp
  rcases hp with ⟨rfl,_⟩
  intro i
  cases k <;> (by_cases hi : i=a.cell <;> simp [SdkState.put,hi])

structure SnapshotFacts (a : AccountInfo) (l1 l2 : Nat) (s t : SdkState)
    (x : OwnedAccount) : Prop where
  frame : PayloadFrame s t
  consistent : TX2_241.Consistent x
  origin : ∀ d, x.bytes=.ok d → d=payload a s
  extent : ∀ d, x.bytes=.ok d → d.length=l1 ∨ d.length=l2

theorem snapshot_facts (a : AccountInfo) (l1 l2 : Nat) (s t : SdkState)
    (x : OwnedAccount) (env : Env) (es : List Event)
    (h : snapshot a l1 l2 s env ⟨.ret (x,t),es⟩) : SnapshotFacts a l1 l2 s t x := by
  obtain ⟨r,e1,e2,ha,hk,_⟩ := bind_return _ _ _ _ _ h
  have hf := acquire_frame a .shared s r.2 r.1 env e1 ha
  rcases r with ⟨reply,s1⟩
  cases reply with
  | error e =>
    simp only [Spec.pure, Obs.mk.injEq, Exit.ret.injEq, Prod.mk.injEq] at hk
    rcases hk with ⟨⟨rfl,rfl⟩,_⟩
    refine ⟨hf,?_,?_,?_⟩
    · intro d hd; cases hd
    · intro d hd; cases hd
    · intro d hd; cases hd
  | ok token =>
    obtain ⟨_,_,e3,_,hk,_⟩ := bind_return _ _ _ _ _ hk
    obtain ⟨s2,_,_,hr,hp,_⟩ := bind_return _ _ _ _ _ hk
    have hg := release_frame a token .shared s1 s2 env _ hr
    simp only [Spec.pure, Obs.mk.injEq, Exit.ret.injEq, Prod.mk.injEq] at hp
    rcases hp with ⟨⟨rfl,rfl⟩,_⟩
    refine ⟨frame_trans hf hg,?_,?_,?_⟩
    · intro d hd
      split at hd
      · cases hd; rfl
      · cases hd
    · intro d hd
      split at hd
      · cases hd; exact hf a.cell
      · cases hd
    · intro d hd
      split at hd
      next admitted =>
        cases hd
        simpa only [Bool.or_eq_true, beq_iff_eq] using admitted
      · cases hd

#print axioms frame_refl
#print axioms frame_trans
#print axioms bind_return
#print axioms emit_return
#print axioms acquire_frame
#print axioms release_frame
#print axioms snapshot_facts
end NMV_RslLaws
