import AllocationStageSpecM10

/-! Attach a proved constructor counter without unfolding a concrete stage's
implementation while checking the dependent allocation field. -/
set_option autoImplicit false
namespace AspisR1.AllocationStageAttachM10

def attach {A B : Type} {f : A → Option B} {I : A → Prop} {J : B → Prop}
    {F : Nat → Nat} (W : Nat) (s : AbstractStageSpecM10.StageSpec f I J F)
    (heap : A → Nat) (paid : ∀ a, heap a ≤ (s.run a).2) :
    AllocationStageSpecM10.StageSpec W f I J F where
  toStageSpec := s
  allocation a := ⟨heap a,W*heap a,Nat.le_refl _,paid a⟩

theorem run {A B : Type} {f : A → Option B} {I : A → Prop} {J : B → Prop}
    {F : Nat → Nat} (W : Nat) (s : AbstractStageSpecM10.StageSpec f I J F)
    (heap : A → Nat) (paid : ∀ a, heap a ≤ (s.run a).2) (a : A) :
    (attach W s heap paid).run a = s.run a := rfl

#print axioms run
end AspisR1.AllocationStageAttachM10
