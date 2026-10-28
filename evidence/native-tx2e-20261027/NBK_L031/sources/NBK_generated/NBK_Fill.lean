import NBH_Audit
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NBK_Fill

theorem constant (xs : List U8) (v : U8) :
    List.mapM (fun _ => ok v) xs = ok (List.replicate xs.length v) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM,ih,pure]

def value (s : Slice U8) (v : U8) : Slice U8 :=
  ⟨List.replicate s.length v, by simpa only [List.length_replicate,Slice.length] using s.property⟩

theorem source (s : Slice U8) (v : U8) :
    core.slice.Slice.fill core.clone.CloneU8 s v = ok (value s v) := by
  unfold core.slice.Slice.fill
  have clone : core.clone.CloneU8.clone v = ok v := rfl
  simp only [clone,constant]
  rfl

#print axioms constant
#print axioms source
end NBK_Fill
