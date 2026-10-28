import NBH_Audit
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NBK_Fill

theorem loop (xs acc : List U8) (v : U8) :
    List.mapM.loop (fun _ : U8 => ok v) xs acc =
      ok (acc.reverse ++ List.replicate xs.length v) := by
  induction xs generalizing acc with
  | nil => simp [List.mapM.loop,pure]
  | cons x xs ih => simp [List.mapM.loop,ih,pure,List.reverse_cons,List.replicate_succ,List.append_assoc]

theorem constant (xs : List U8) (v : U8) :
    List.mapM (fun _ => ok v) xs = ok (List.replicate xs.length v) := by
  simpa only [List.mapM,List.reverse_nil,List.nil_append] using loop xs [] v

def value (s : Slice U8) (v : U8) : Slice U8 :=
  ⟨List.replicate s.length v, by simpa only [List.length_replicate,Slice.length] using s.property⟩

theorem source (s : Slice U8) (v : U8) :
    core.slice.Slice.fill core.clone.CloneU8 s v = ok (value s v) := by
  unfold core.slice.Slice.fill
  simp only [core.clone.CloneU8,liftFun1,core.clone.impls.CloneU8.clone,lift]
  split
  next out hm =>
    have fact := constant s.val v
    rw [hm] at fact
    have same := Result.ok.inj fact
    subst out
    rfl
  next e hm =>
    have fact := constant s.val v
    rw [hm] at fact
    cases fact
  next hm =>
    have fact := constant s.val v
    rw [hm] at fact
    cases fact

#print axioms loop
#print axioms constant
#print axioms source
end NBK_Fill
