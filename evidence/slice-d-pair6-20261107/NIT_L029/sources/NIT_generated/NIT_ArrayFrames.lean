import NIT_Cuts
set_option autoImplicit false
namespace AspisR1.NIT_ArrayFrames
open Aeneas Aeneas.Std Result

def pick {T : Type} {n : Usize} (fallback : T) (xs : Array T n) (i : Nat) : T :=
 xs.val[i]?.getD fallback

def put {T : Type} {n : Usize} (xs : Array T n) (i : Nat) (x : T) : Array T n :=
 ⟨xs.val.set i x,by simpa only [List.length_set] using xs.property⟩

theorem ext {T : Type} {n : Usize} (fallback : T) (xs ys : Array T n)
 (same : ∀ i,i<n.val → pick fallback xs i=pick fallback ys i) : xs=ys := by
 apply Subtype.ext
 apply List.ext_getElem?
 intro i
 by_cases hi : i<n.val
 · have hx : i<xs.val.length := by rw [xs.property];exact hi
   have hy : i<ys.val.length := by rw [ys.property];exact hi
   have h := same i hi
   simp only [pick,List.getElem?_eq_getElem hx,List.getElem?_eq_getElem hy,Option.getD_some] at h
   simp only [List.getElem?_eq_getElem hx,List.getElem?_eq_getElem hy,h]
 · have hx : xs.val.length ≤ i := by rw [xs.property];omega
   have hy : ys.val.length ≤ i := by rw [ys.property];omega
   simp only [List.getElem?_eq_none hx,List.getElem?_eq_none hy]

theorem pick_put {T : Type} {n : Usize} (fallback : T) (xs : Array T n)
 (i : Nat) (x : T) (hi : i<n.val) (k : Nat) :
 pick fallback (put xs i x) k=if k=i then x else pick fallback xs k := by
 have hx : i<xs.val.length := by rw [xs.property];exact hi
 by_cases same : k=i
 · subst k
   simp [pick,put,List.getElem?_set,hx,hi]
 · simp [pick,put,List.getElem?_set,same,Ne.symm same]

/-- The all-cell native observation determines the full array update. -/
theorem update {T : Type} {n : Usize} (fallback : T) (before after : Array T n)
 (i : Nat) (reply : T) (hi : i<n.val)
 (frame : ∀ k,k<n.val → pick fallback after k=if k=i then reply else pick fallback before k) :
 after=put before i reply := by
 apply ext fallback
 intro k hk
 rw [frame k hk,pick_put fallback before i reply hi k]

#print axioms ext
#print axioms pick_put
#print axioms update
end AspisR1.NIT_ArrayFrames
