import NMV_RslLaws
set_option autoImplicit false
namespace NMV_RslSnapshots
open RSL NMV_RslLaws

structure Image (s : SdkState) (a : AccountInfo) (lens : Nat × Nat) (x : OwnedAccount) : Prop where
 consistent : TX2_241.Consistent x
 origin : ∀ d, x.bytes=.ok d → d=payload a s
 extent : ∀ d, x.bytes=.ok d → d.length=lens.1 ∨ d.length=lens.2

def Images (s : SdkState) : List AccountInfo → List (Nat × Nat) → List OwnedAccount → Prop
 | a::as,l::ls,x::xs => Image s a l x ∧ Images s as ls xs
 | _,_,[] => True
 | _,_,_::_ => False

theorem image_back {s t : SdkState} (frame : PayloadFrame s t)
 (a : AccountInfo) (l : Nat × Nat) (x : OwnedAccount) (h : Image t a l x) : Image s a l x :=
 ⟨h.consistent,fun d hd => (h.origin d hd).trans (frame a.cell),h.extent⟩

theorem images_back {s t : SdkState} (frame : PayloadFrame s t)
 (as : List AccountInfo) (ls : List (Nat × Nat)) (xs : List OwnedAccount)
 (h : Images t as ls xs) : Images s as ls xs := by
 induction as generalizing ls xs with
 | nil => cases xs <;> simpa [Images] using h
 | cons a as ih =>
   cases ls with
   | nil => cases xs <;> simpa [Images] using h
   | cons l ls =>
     cases xs with
     | nil => trivial
     | cons x xs => exact ⟨image_back frame a l x h.1, ih ls xs h.2⟩

theorem snapAll_facts (as : List AccountInfo) (ls : List (Nat × Nat))
 (s t : SdkState) (xs : List OwnedAccount) (env : Env) (es : List Event)
 (h : TX2_240.snapAll as ls s env ⟨.ret (xs,t),es⟩) :
 PayloadFrame s t ∧ Images s as ls xs := by
 induction as generalizing ls s t xs es with
 | nil =>
   simp only [TX2_240.snapAll, Spec.pure, Obs.mk.injEq, Exit.ret.injEq, Prod.mk.injEq] at h
   rcases h with ⟨⟨rfl,rfl⟩,_⟩
   exact ⟨frame_refl _,trivial⟩
 | cons a as ih =>
   cases ls with
   | nil =>
     simp only [TX2_240.snapAll, Spec.pure, Obs.mk.injEq, Exit.ret.injEq, Prod.mk.injEq] at h
     rcases h with ⟨⟨rfl,rfl⟩,_⟩
     exact ⟨frame_refl _,trivial⟩
   | cons l ls =>
     obtain ⟨⟨x,s1⟩,e1,e2,hx,hk,_⟩ := bind_return _ _ _ _ _ h
     have f := snapshot_facts a l.1 l.2 s s1 x env e1 hx
     obtain ⟨⟨ys,s2⟩,e3,e4,hy,hp,_⟩ := bind_return _ _ _ _ _ hk
     have g := ih ls s1 s2 ys e3 hy
     simp only [Spec.pure, Obs.mk.injEq, Exit.ret.injEq, Prod.mk.injEq] at hp
     rcases hp with ⟨⟨rfl,rfl⟩,_⟩
     exact ⟨frame_trans f.frame g.1, ⟨⟨f.consistent,f.origin,f.extent⟩,
       images_back f.frame as ls ys g.2⟩⟩

theorem images_consistent (s : SdkState) (as : List AccountInfo)
 (ls : List (Nat × Nat)) (xs : List OwnedAccount) (h : Images s as ls xs) :
 ∀ x ∈ xs, TX2_241.Consistent x := by
 induction xs generalizing as ls with
 | nil => simp
 | cons x xs ih =>
   cases as with
   | nil => cases h
   | cons a as =>
     cases ls with
     | nil => cases h
     | cons l ls =>
       intro y hy
       rcases List.mem_cons.mp hy with rfl | hy
       · exact h.1.consistent
       · exact ih as ls h.2 y hy

theorem images_lookup (s : SdkState) (as : List AccountInfo)
 (ls : List (Nat × Nat)) (xs : List OwnedAccount) (h : Images s as ls xs)
 (i : Nat) (x : OwnedAccount) (hx : xs[i]?=some x) :
 ∃ a l, as[i]?=some a ∧ ls[i]?=some l ∧ Image s a l x := by
 induction xs generalizing as ls i with
 | nil => simp at hx
 | cons y ys ih =>
   cases as with
   | nil => cases h
   | cons a as =>
     cases ls with
     | nil => cases h
     | cons l ls =>
       cases i with
       | zero =>
         simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
         subst x
         exact ⟨a,l,rfl,rfl,h.1⟩
       | succ i =>
         exact ih as ls h.2 i (by simpa using hx)

#print axioms image_back
#print axioms images_back
#print axioms snapAll_facts
#print axioms images_consistent
#print axioms images_lookup
end NMV_RslSnapshots
