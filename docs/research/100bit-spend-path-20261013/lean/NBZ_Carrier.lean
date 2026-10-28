import NBW_Audit
set_option autoImplicit false
namespace NBZ_Carrier
open Aeneas Aeneas.Std Result
/-- Same finite native-model vector throughout: each next window writes the
retained source value at its actual ordinal. There is no independent final
buffer or pointwise final-equality hypothesis. Capacity/provenance are native
metadata duties; the cohort Vec represents initialized values and length. -/
inductive Fill {α : Type} (source : Nat → α) :
 Nat → Nat → alloc.vec.Vec α → alloc.vec.Vec α → Prop
 | nil (start : Nat) (raw : alloc.vec.Vec α) : Fill source start 0 raw raw
 | step {start count : Nat} {before mid : alloc.vec.Vec α}
   (prior : Fill source start count before mid) (index : Usize)
   (ordinal : index.val=start+count) (active : index.val<mid.val.length) :
   Fill source start (count+1) before (mid.set index (source index.val))
/-- Copy windows preserve the actual finite carrier's extent. -/
theorem length {α : Type} {source : Nat → α} {start count : Nat}
 {before after : alloc.vec.Vec α} (trace : Fill source start count before after) :
 after.val.length=before.val.length := by
 induction trace with
 | nil => rfl
 | step prior index ordinal active ih =>
   change (List.set _ _ _).length=_
   rw [List.length_set,ih]
/-- Native single-window effect/frame observations compose on the SAME Vec,
with the exact KMX value law. This covers arbitrary symbolic precontents. -/
theorem value {α : Type} {source : Nat → α} {start count : Nat}
 {before after : alloc.vec.Vec α} (trace : Fill source start count before after)
 (j : Nat) :
 after.val[j]?=KMX_CopyMeaning.loop (fun i=>some (source i))
   (fun i=>before.val[i]?) start count j := by
 induction trace with
 | nil =>
   simp only [KMX_CopyMeaning.loop_spec]
   rw [if_neg (by omega)]
 | @step count before mid prior index ordinal active ih =>
   change (mid.val.set index.val (source index.val))[j]?=_
   rw [List.getElem?_set]
   by_cases eq : j=index.val
   · subst j
     simp only [if_pos rfl,active,if_pos]
     rw [KMX_CopyMeaning.loop_spec,if_pos (by omega)]
   · simp only [if_neg eq,if_neg (Ne.symm eq)]
     rw [ih,KMX_CopyMeaning.loop_spec,KMX_CopyMeaning.loop_spec]
     by_cases inside : start≤j ∧ j<start+count
     · rw [if_pos inside,if_pos (by omega)]
     · rw [if_neg inside,if_neg (by omega)]
/-- Full initialized-value/frame statement plus unchanged length, suitable
for a native window gate on a retained allocation. -/
theorem window {α : Type} {source : Nat → α} {start count : Nat}
 {before after : alloc.vec.Vec α} (trace : Fill source start count before after) :
 after.val.length=before.val.length ∧
 (∀ j, after.val[j]?=KMX_CopyMeaning.loop (fun i=>some (source i))
   (fun i=>before.val[i]?) start count j) :=
 ⟨length trace,value trace⟩
#print axioms length
#print axioms value
#print axioms window
end NBZ_Carrier
