import AllocationStageAttachM10
import ConstantStagePackM10

set_option autoImplicit false
namespace AspisR1.AllocationConstantStagePackM10

def pack {A B : Type} (W : Nat) (f : A → Option B) (J : B → Prop) (C : Nat)
    (r : A → Option B × Nat) (hv : ∀ a, (r a).1 = f a)
    (hw : ∀ a, (r a).2 ≤ C) (hi : ∀ a b, (r a).1 = some b → J b)
    (heap : A → Nat) (hp : ∀ a, heap a ≤ (r a).2) :
    AllocationStageSpecM10.StageSpec W f (fun _ => True) J (fun _ => C) :=
  AllocationStageAttachM10.attach W (ConstantStagePackM10.pack f J C r hv hw hi) heap hp

end AspisR1.AllocationConstantStagePackM10
