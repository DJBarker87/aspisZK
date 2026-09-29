import AspisV8R19.DescendingRemainder
import AspisV8R19.SourceMaskBoundary

/-! Source loop ordering and bounded sequential writes, in exact-field
semantics. This is not an Aeneas extraction or Rust word-refinement claim. -/
namespace AspisR19.NormalizationLoopBridge
open AspisV8R17 SourceFactorEvaluation DescendingRemainder HighRepairInvariant
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem shift_seed (roots : List F) :
    shift roots 0=(roots.foldl (buildStep (2:F)⁻¹)
      (0,fun i => if i=0 then 1 else 0)).2 := by
  have h := congrArg Prod.snd (build_factor (2:F)⁻¹ roots [])
  simpa only [shift,List.replicate_zero,List.nil_append,List.length_nil,
    FactorLeading.factor,List.append_nil] using h.symm

theorem shift_next (roots : List F) (hl : roots.length=22) (k : Nat) :
    shift roots (k+1)=scatterValue (sourceEdges (2:F)⁻¹ (23+k)) (shift roots k) := by
  funext i
  simp only [shift,List.replicate_succ,List.cons_append,FactorLeading.factor,
    List.length_append,List.length_replicate,List.length_reverse,hl,zero_mul,sub_zero]
  congr 2
  omega

theorem writes_prefix (n : Nat) (v w : Nat → F) (f : F) :
    (List.range n).foldl (fun state j => Function.update state j (state j-f*w j)) v=
      fun i => if i<n then v i-f*w i else v i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,ih]
    funext i
    by_cases he : i=n
    · subst i; simp
    · by_cases hi : i<n
      · simp [Function.update_apply,he,hi,show i<n+1 by omega]
      · simp [Function.update_apply,he,hi,show ¬i<n+1 by omega]

theorem writes_step (roots : List F) (k : Nat) (v : Nat → F) :
    (List.range (22+k+1)).foldl
      (fun state j => Function.update state j
        (state j-(v (22+k)*(shift roots k (22+k))⁻¹)*shift roots k j)) v=
      step roots k v := by
  rw [writes_prefix]
  funext i
  simp only [step,Nat.lt_succ_iff]

theorem descending_order (roots : List F) (n : Nat) (v : Nat → F) :
    (List.range n).reverse.foldl (fun state k => step roots k state) v=reduce roots n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ,List.reverse_append,List.reverse_singleton,
      List.singleton_append,List.foldl_cons,ih,reduce]

def finished (roots : List F) (d : Fin 32) (i : Fin 32) : F :=
  if i=d then 1 else -remainder roots d i.val

theorem finished_eq (t : Fin 22 → F) (ht : Function.Injective t) (d : Fin 32)
    (hd : 22≤d.val) (i : Fin 32) :
    finished (List.ofFn t) d i=NormalizedQuerySection.normalized t ht d i := by
  rw [← normalized_remainder t ht d hd i]
  by_cases h : i=d
  · subst i
    rw [finished,if_pos rfl,remainder_support _ (by simp) d hd d.val hd]
    simp [DescendingRemainder.unit]
  · simp [finished,h,DescendingRemainder.unit,show i.val≠d.val from fun he => h (Fin.ext he)]

def sourceQuotient (t : Fin 22 → F) (alpha : F) (d : Fin 32) (s : Fin 4) (i : Index 32) : F :=
  if i.2=0 then -(alpha^s.val)*finished (List.ofFn t) d i.1
  else if i.2=s then finished (List.ofFn t) d i.1 else 0

theorem sourceQuotient_eq (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
    (d : Fin 32) (hd : 22≤d.val) (s : Fin 4) (hs : s≠0) :
    sourceQuotient t alpha d s=NormalizedQuotient.quotient t ht alpha d s := by
  funext i
  simp only [sourceQuotient,finished_eq t ht d hd,NormalizedQuotient.quotient,
    NormalizedQuotient.slotFactor]
  by_cases hz : i.2=0 <;> by_cases he : i.2=s <;> simp_all <;> ring

theorem selected_sourceQuotient_eq (t : Fin 22 → F) (ht : Function.Injective t)
    (alpha : F) (j : Fin 13) :
    sourceQuotient t alpha (SparseHighWitness.degree j) (SparseHighWitness.slot j)=
      NormalizedQuotient.quotient t ht alpha (SparseHighWitness.degree j) (SparseHighWitness.slot j) := by
  apply sourceQuotient_eq t ht alpha
  · simp only [SparseHighWitness.degree]
    split_ifs <;> omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [SparseHighWitness.slot,Fin.val_zero] at hv
    split_ifs at hv <;> omega

#print axioms shift_seed
#print axioms shift_next
#print axioms writes_prefix
#print axioms writes_step
#print axioms descending_order
#print axioms finished_eq
#print axioms sourceQuotient_eq
#print axioms selected_sourceQuotient_eq
end
end AspisR19.NormalizationLoopBridge
