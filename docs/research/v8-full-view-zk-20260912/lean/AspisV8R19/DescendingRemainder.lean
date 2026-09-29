import AspisV8R19.SourceFactorEvaluation
import AspisV8R19.NormalizedQuerySection

/-! The descending scalar algorithm, including its bounded update range.
No pivot/nonvanishing or evaluation premise is assumed: all are supplied
by the source-shaped factor construction. Machine-word refinement is separate. -/
namespace AspisR19.DescendingRemainder
open AspisCircleTensorBinding SourceFactorEvaluation
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def step (roots : List F) (k : Nat) (v : Nat → F) (i : Nat) : F :=
  if i ≤ 22+k then v i-(v (22+k)*(shift roots k (22+k))⁻¹)*shift roots k i else v i

theorem step_full (roots : List F) (hl : roots.length=22) (k : Nat) (hk : k<10)
    (v : Nat → F) : step roots k v=
      fun i => v i-(v (22+k)*(shift roots k (22+k))⁻¹)*shift roots k i := by
  funext i
  by_cases h : i ≤ 22+k
  · simp [step,h]
  · rw [step,if_neg h,shift_support roots hl k hk i (by omega)]
    simp

theorem step_pivot (roots : List F) (hl : roots.length=22) (k : Nat) (hk : k<10)
    (v : Nat → F) : step roots k v (22+k)=0 := by
  rw [step_full roots hl k hk]
  simp only [mul_assoc,inv_mul_cancel₀ (shift_pivot_ne_zero roots hl k hk),mul_one,sub_self]

theorem step_support (roots : List F) (hl : roots.length=22) (k : Nat) (hk : k<10)
    (v : Nat → F) (hv : ∀ i, 22+k < i → v i=0) :
    ∀ i, 22+k ≤ i → step roots k v i=0 := by
  intro i hi
  by_cases he : i=22+k
  · subst i; exact step_pivot roots hl k hk v
  · have h : ¬i ≤ 22+k := by omega
    simpa only [step,if_neg h] using hv i (by omega)

theorem step_evaluation (roots : List F) (hl : roots.length=22) (k : Nat) (hk : k<10)
    (v : Nat → F) (x : F) (hx : x∈roots) : line 32 (step roots k v) x=line 32 v x := by
  rw [step_full roots hl k hk,line_sub,shift_root roots hl k hk x hx,mul_zero,sub_zero]

def reduce (roots : List F) : Nat → (Nat → F) → Nat → F
  | 0,v => v
  | n+1,v => reduce roots n (step roots n v)

theorem reduce_support (roots : List F) (hl : roots.length=22) (n : Nat) (hn : n≤10)
    (v : Nat → F) (hv : ∀ i, 22+n ≤ i → v i=0) :
    ∀ i, 22 ≤ i → reduce roots n v i=0 := by
  induction n generalizing v with
  | zero => exact hv
  | succ n ih =>
    exact ih (by omega) (step roots n v)
      (step_support roots hl n (by omega) v (fun i hi => hv i (by omega)))

theorem reduce_evaluation (roots : List F) (hl : roots.length=22) (n : Nat) (hn : n≤10)
    (v : Nat → F) (x : F) (hx : x∈roots) : line 32 (reduce roots n v) x=line 32 v x := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [reduce,ih (by omega),step_evaluation roots hl n (by omega) v x hx]

def unit (d i : Nat) : F := if i=d then 1 else 0
def remainder (roots : List F) (d : Fin 32) : Nat → F :=
  reduce roots (d.val+1-22) (unit d.val)

theorem remainder_support (roots : List F) (hl : roots.length=22) (d : Fin 32) (hd : 22≤d.val) :
    ∀ i, 22 ≤ i → remainder roots d i=0 := by
  apply reduce_support roots hl _ (by have := d.isLt; omega)
  intro i hi
  simp only [unit,if_neg (show i≠d.val by omega)]

theorem remainder_evaluation (roots : List F) (hl : roots.length=22) (d : Fin 32)
    (x : F) (hx : x∈roots) : line 32 (remainder roots d) x=naturalLineValue x d.val := by
  rw [remainder,reduce_evaluation roots hl _ (by have := d.isLt; omega) _ x hx]
  simp [line,unit,d.isLt]

theorem remainder_is_low (t : Fin 22 → F) (ht : Function.Injective t) (d : Fin 32)
    (hd : 22≤d.val) :
    (fun i : Fin 22 => remainder (List.ofFn t) d i.val)=NormalizedQuerySection.low t ht d := by
  apply NormalizedQuerySection.low_unique t ht d
  funext j
  have h := remainder_evaluation (List.ofFn t) (by simp) d (t j)
    (List.mem_ofFn.mpr ⟨j,rfl⟩)
  rw [← line_restrict 22 32 (by decide) _
    (fun i hi _ => remainder_support (List.ofFn t) (by simp) d hd i hi)] at h
  rw [line,Finset.sum_range] at h
  simpa only [Matrix.mulVec,dotProduct,naturalEvalMatrix,naturalLineValue_eq_eval] using h

theorem normalized_remainder (t : Fin 22 → F) (ht : Function.Injective t)
    (d : Fin 32) (hd : 22≤d.val) (i : Fin 32) :
    unit d.val i.val-remainder (List.ofFn t) d i.val=NormalizedQuerySection.normalized t ht d i := by
  have he : unit (F:=F) d.val i.val=(if i=d then 1 else 0) := by simp [unit,Fin.ext_iff]
  rw [he,NormalizedQuerySection.normalized]
  congr 1
  by_cases hi : i.val<22
  · have h := congrFun (remainder_is_low t ht d hd) ⟨i.val,hi⟩
    simpa only [NormalizedQuerySection.extendLow,dif_pos hi] using h
  · rw [NormalizedQuerySection.extendLow,dif_neg hi,remainder_support _ (by simp) d hd i.val (by omega)]

#print axioms step_full
#print axioms step_pivot
#print axioms step_support
#print axioms step_evaluation
#print axioms reduce_support
#print axioms reduce_evaluation
#print axioms remainder_support
#print axioms remainder_evaluation
#print axioms remainder_is_low
#print axioms normalized_remainder
end
end AspisR19.DescendingRemainder
