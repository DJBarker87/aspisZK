import NJL_TagData
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumIntervals

def intervals (off : Nat → Nat) (n : Nat) : List Nat :=
 (List.range n).flatMap (fun c=>List.range' (off c) (off (c+1)-off c))

theorem partition (off : Nat → Nat) (mono : Monotone off) (n : Nat) :
 intervals off n=List.range' (off 0) (off n-off 0) := by
 induction n with
 | zero => simp [intervals]
 | succ n ih =>
  have first : off 0≤off n := mono (Nat.zero_le n)
  have next : off n≤off (n+1) := mono (Nat.le_succ n)
  have start : off 0+(off n-off 0)=off n := by omega
  have length : (off n-off 0)+(off (n+1)-off n)=off (n+1)-off 0 := by omega
  simp only [intervals,List.range_succ,List.flatMap_append,List.flatMap_singleton] at ih ⊢
  rw [ih]
  have second : List.range' (off n) (off (n+1)-off n)=
   List.range' (off 0+(off n-off 0)) (off (n+1)-off n) :=
   congrArg (fun a=>List.range' a (off (n+1)-off n)) start.symm
  rw [second]
  first
  | rw [←List.range'_append,length]
  | rw [List.range'_append,length]

def off (n : Nat) : Nat := NJL_TagData.offsets ⟨min n 30,by omega⟩

theorem step (n : Nat) : off n≤off (n+1) := by
 by_cases small : n<30
 · have h := (NJL_TagData.interval ⟨n,small⟩).1.le
   simpa only [off,Nat.min_eq_left (Nat.le_of_lt small),Nat.min_eq_left (by omega),
    NJL_TagData.first,NJL_TagData.last] using h
 · have hn : 30≤n := by omega
   have hn' : 30≤n+1 := by omega
   simp only [off,Nat.min_eq_right hn,Nat.min_eq_right hn']

theorem monotone : Monotone off := by
 intro i j hij
 induction j,hij using Nat.le_induction with
 | base => exact Nat.le_refl _
 | succ j hij ih => exact ih.trans (step j)

theorem thirty : intervals off 30=List.range 272 := by
 rw [partition off monotone]
 rfl

/-- Generic map/flatMap laws keep the272positions symbolic. -/
theorem map_flatMap {A B C : Type} (f : A → List B) (v : B → C) (xs : List A) :
 (xs.flatMap f).map v=xs.flatMap (fun a=>(f a).map v) := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp only [List.flatMap_cons,List.map_append,ih]

theorem fin_values (n : Nat) : (List.finRange n).map Fin.val=List.range n := by
 apply List.ext_getElem
 · simp
 · intro i hi hj
   simp

theorem lists_ext {n : Nat} (xs ys : List (Fin n)) (h : xs.map Fin.val=ys.map Fin.val) : xs=ys := by
 induction xs generalizing ys with
 | nil =>
  cases ys with
  | nil => rfl
  | cons y ys => simp at h
 | cons x xs ih =>
  cases ys with
  | nil => simp at h
  | cons y ys =>
   simp only [List.map_cons,List.cons.injEq] at h
   have xy : x=y := Fin.ext h.1
   subst y
   exact congrArg (List.cons x) (ih ys h.2)

#print axioms partition
#print axioms step
#print axioms monotone
#print axioms thirty
#print axioms map_flatMap
#print axioms fin_values
#print axioms lists_ext
end AspisR1.NKR_SumIntervals
end
