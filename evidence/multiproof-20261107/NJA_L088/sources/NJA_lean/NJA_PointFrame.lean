import Aeneas

set_option autoImplicit false
namespace NJA_PointFrame
variable {α : Type} {width : Nat}
abbrev State (width : Nat) (α : Type) := Fin width → α

def write (s : State width α) (i : Fin width) (x : α) : State width α :=
 fun k => if k=i then x else s k

def processed (s : State width α) (f : Fin width → α → α) (n : Nat) : State width α :=
 fun i => if i.val<n then f i (s i) else s i

theorem current (s : State width α) (f : Fin width → α → α) (i : Fin width) :
 processed s f i.val i = s i := by simp [processed]

theorem same (s : State width α) (i : Fin width) (x : α) : write s i x i = x := by simp [write]

theorem other (s : State width α) (i k : Fin width) (x : α) (h : k≠i) :
 write s i x k = s k := by simp [write,h]

theorem step (s : State width α) (f : Fin width → α → α) (i : Fin width) :
 write (processed s f i.val) i (f i (processed s f i.val i)) = processed s f (i.val+1) := by
 rw [current]
 funext k
 by_cases eq : k=i
 · subst k;simp [write,processed]
 · have ne : k.val≠i.val := by intro h;exact eq (Fin.ext h)
   have p : k.val < i.val+1 ↔ k.val < i.val := by omega
   simp [write,processed,eq,p]

def run (s : State width α) (f : Fin width → α → α) : Nat → State width α
 | 0 => s
 | n+1 => if h : n<width then write (run s f n) ⟨n,h⟩ (f ⟨n,h⟩ (run s f n ⟨n,h⟩))
   else run s f n

theorem run_prefix (s : State width α) (f : Fin width → α → α) (n : Nat) (h : n≤width) :
 run s f n = processed s f n := by
 induction n with
 | zero => funext i;simp [run,processed]
 | succ n ih =>
   have a : n<width := by omega
   rw [run,dif_pos a,ih (by omega)]
   exact step s f ⟨n,a⟩

theorem complete (s : State width α) (f : Fin width → α → α) :
 run s f width = fun i => f i (s i) := by
 rw [run_prefix s f width (by omega)]
 funext i
 simp [processed,i.isLt]

theorem frame (s : State width α) (f : Fin width → α → α) (n : Nat) (h : n≤width)
 (i : Fin width) (hi : n≤i.val) : run s f n i = s i := by
 rw [run_prefix s f n h]
 simp [processed,show ¬i.val<n by omega]

#print axioms current
#print axioms same
#print axioms other
#print axioms step
#print axioms run_prefix
#print axioms complete
#print axioms frame
end NJA_PointFrame
