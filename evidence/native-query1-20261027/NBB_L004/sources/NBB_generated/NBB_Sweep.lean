import NBB_Phase
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBB_Sweep
def Bound (t : Nat) (row : Array U64 4#usize) : Prop := ∀ x∈row.val, NBB_Phase.Bound t x.val
abbrev Raw := alloc.vec.Vec (Array U64 4#usize)
/-- Rows before the real cursor have advanced; all other rows retain the
current query's phase. The query term counter is incremented only afterwards. -/
def Inv (t cursor : Nat) (raw : Raw) : Prop := ∀ j row,
 raw.val[j]?=some row → Bound (if j<cursor then t+1 else t) row

theorem initial (t : Nat) (raw : Raw) (phase : ∀ row∈raw.val,Bound t row) : Inv t 0 raw := by
 intro j row get
 simpa only [Nat.not_lt_zero,if_false] using phase row (List.mem_of_getElem? get)
/-- One setter advances precisely the newly processed row; all other rows
retain their previous phase and position, including arbitrary suffixes. -/
theorem update (t j : Nat) (raw : Raw) (row : (Array U64 4#usize)) (i : Usize)
 (same : i.val=j) (inv : Inv t j raw) (done : Bound (t+1) row) :
 Inv t (j+1) (raw.set i row) := by
 intro k value get
 change (raw.val.set i.val row)[k]?=some value at get
 by_cases eq : k=j
 · subst k
   have len : j<raw.val.length := by
    have len : j<(raw.val.set i.val row).length := (List.getElem?_eq_some_iff.mp get).1
    simpa only [List.length_set] using len
   rw [same,List.getElem?_set_self len] at get
   cases Option.some.inj get
   simpa only [Nat.lt_succ_self,if_true] using done
 · have get0 : raw.val[k]?=some value := by
    simpa only [same,List.getElem?_set,if_neg eq,if_neg (Ne.symm eq)] using get
   have old := inv k value get0
   have iff : (k<j+1)↔k<j := by omega
   simpa only [iff] using old

theorem final (t width : Nat) (raw : Raw) (len : raw.val.length≤width)
 (inv : Inv t width raw) : ∀ row∈raw.val,Bound (t+1) row := by
 intro row mem
 obtain ⟨j,get⟩ := List.mem_iff_getElem?.mp mem
 have lt : j<width := by have := (List.getElem?_eq_some_iff.mp get).1;omega
 simpa only [if_pos lt] using inv j row get
#print axioms initial
#print axioms update
#print axioms final
end NBB_Sweep
