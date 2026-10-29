import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD4_TryArray194
open Aeneas Aeneas.Std Result
/-- Owned value projection of slice-to-fixed-array conversion. No copy builtin
or pointer alias theorem is assumed; those source bindings remain separate. -/
def into {T : Type} (n : Usize) (xs : List T) : Option (Array T n) :=
  if size : xs.length=n.val then some ⟨xs,size⟩ else none

theorem success {T : Type} (n : Usize) (xs : List T) (size : xs.length=n.val) :
    into n xs = some ⟨xs,size⟩ := dif_pos size

theorem mismatch {T : Type} (n : Usize) (xs : List T) (size : xs.length≠n.val) :
    into n xs = none := dif_neg size

theorem backing {T : Type} (n : Usize) (xs : List T) :
    (into n xs).map (fun out => out.val) =
      if xs.length=n.val then some xs else none := by
  unfold into
  split <;> rfl

theorem roundtrip {T : Type} {n : Usize} (xs : Array T n) :
    into n xs.val = some xs := by
  rw [success n xs.val xs.property]
#print axioms success
#print axioms mismatch
#print axioms backing
#print axioms roundtrip
end R1Z.PV_RDCD4_TryArray194
