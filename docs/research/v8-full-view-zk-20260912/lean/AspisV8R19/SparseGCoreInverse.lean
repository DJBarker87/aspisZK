/- Explicit sparse minor at alpha=1 and identity chord. This is an algebraic
   witness, NOT an admissible sampled transcript or an oracle-law theorem. -/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace AspisR19.SparseGCoreInverse
variable {F : Type*} [CommRing F]

def block (x : Nat → F) (i : Nat) : F :=
  if i % 4 = 0 then -x i - x (i+1) else x i

theorem block_involution (x : Nat → F) : block (block x) = x := by
  funext i
  by_cases h : i % 4 = 0
  · have hn : (i+1)%4 ≠ 0 := by omega
    simp only [block,if_pos h,if_neg hn]
    ring
  · simp only [block,if_neg h]

/- Chosen high columns in the 699-dimensional direct quotient section.
   Each group supplies q[4d+k]=u[d,k], q[4d]=-sum_k u[d,k] at alpha=1.
   Three successive groups use channels {1,3}, {2}, {1}. -/
def channel (x : Nat → F) (d k : Nat) : F :=
  if d < 32 then 0 else
  let b := (d-32)/3
  if (d-32)%3 = 0 then
    if k=1 then x (4*b) else if k=3 then x (4*b+1) else 0
  else if (d-32)%3 = 1 then
    if k=2 then x (4*b+2) else 0
  else if k=1 then x (4*b+3) else 0

def quotient (x : Nat → F) (j : Nat) : F :=
  if j%4=0 then -(channel x (j/4) 1 + channel x (j/4) 2 + channel x (j/4) 3)
  else channel x (j/4) (j%4)

theorem source_block (x : Nat → F) (i : Nat) :
    quotient x (128+3*i) = block x i := by
  have hi : i = 4*(i/4)+i%4 := by omega
  have hm : i%4=0 ∨ i%4=1 ∨ i%4=2 ∨ i%4=3 := by omega
  rcases hm with h|h|h|h
  all_goals
    have hd : (128+3*i)/4 = 32+3*(i/4)+(3*(i%4))/4 := by omega
    have hs : (128+3*i)%4 = (3*(i%4))%4 := by omega
    simp only [quotient,hd,hs,h]
    norm_num only at *
    simp only [channel]
    have hb : ¬32+3*(i/4)+(3*(i%4))/4 < 32 := by omega
    simp only [h] at hb
    norm_num only at hb
    simp only [hb,ite_false]
    have hdiv : (32+3*(i/4)+(3*(i%4))/4-32)/3 = i/4 := by omega
    have hmod : (32+3*(i/4)+(3*(i%4))/4-32)%3 = (3*(i%4))/4 := by omega
    simp only [h] at hdiv hmod
    norm_num only at hdiv hmod
    simp only [hdiv,hmod]
    norm_num [block,h]
    all_goals try { congr 1; omega }
  · have he : 4*(i/4)=i := by omega
    rw [he]; ring

def extend (x : Fin 271 → F) (i : Nat) : F :=
  if h : i<271 then x ⟨i,h⟩ else 0

def finiteBlock (x : Fin 271 → F) (i : Fin 271) : F := block (extend x) i.val

theorem extend_block (x : Fin 271 → F) :
    extend (finiteBlock x) = block (extend x) := by
  funext i
  by_cases h : i<271
  · simp only [extend,dif_pos h,finiteBlock]
  · have hn : ¬i+1<271 := by omega
    simp only [extend,dif_neg h,block,dif_neg hn,neg_zero,sub_zero,ite_self]

theorem finite_involution (x : Fin 271 → F) : finiteBlock (finiteBlock x)=x := by
  funext i
  simp only [finiteBlock,extend_block,congrFun (block_involution (extend x)) i.val,
    extend,dif_pos i.isLt]

theorem finite_bijective : Function.Bijective (@finiteBlock F _) := by
  constructor
  · intro x y h
    have hh := congrArg finiteBlock h
    simpa only [finite_involution] using hh
  · intro y; exact ⟨finiteBlock y, finite_involution y⟩

theorem finite_source_inverse (x : Fin 271 → F) (i : Fin 271) :
    quotient (extend (finiteBlock x)) (128+3*i.val)=x i := by
  rw [source_block]
  exact congrFun (finite_involution x) i

theorem finite_scale (h : F) (x : Fin 271 → F) (i : Fin 271) :
    finiteBlock (fun j => h*x j) i = h*finiteBlock x i := by
  have he : extend (fun j => h*x j) = fun n => h*extend x n := by
    funext n
    unfold extend
    split <;> simp
  simp only [finiteBlock,he,block]
  split <;> ring

def selectedColumn (i : Fin 271) : Nat :=
  3*((128+3*i.val)/4-22) + (if (128+3*i.val)%4=0 then 1 else (128+3*i.val)%4) - 1

theorem selectedColumn_lt (i : Fin 271) : selectedColumn i < 699 := by
  unfold selectedColumn
  split <;> omega

theorem selectedColumn_injective : Function.Injective selectedColumn := by
  intro i j h
  by_cases hi : (128+3*i.val)%4=0 <;> by_cases hj : (128+3*j.val)%4=0
  all_goals
    simp only [selectedColumn,hi,hj,ite_true,ite_false] at h
    apply Fin.ext
    omega

/- The normalized circle chord has an algebraic witness [2,0,0]. Its
   rational-parameter denominators vanish, so it is excluded by the sampler. -/
theorem normalized_chord (u : F) (hu : u*u = -1) :
    (1+u*(-u),u*(-u)-1,-(u+(-u))) = ((2:F),0,0) := by
  have h : u*(-u)=1 := by rw [mul_neg,hu,neg_neg]
  rw [h]; ring

theorem witness_excluded (u : F) (hu : u*u = -1) : 1+u*u=0 := by
  rw [hu]; ring

theorem scaled_block_inverse (h : F) (hh : (2:F)*h=1) (x : Fin 271 → F) :
    (fun i => (2:F)*finiteBlock (fun j => h*finiteBlock x j) i)=x := by
  funext i
  rw [finite_scale,finite_involution,← mul_assoc,hh,one_mul]

#print axioms block_involution
#print axioms source_block
#print axioms extend_block
#print axioms finite_involution
#print axioms finite_bijective
#print axioms finite_source_inverse
#print axioms finite_scale
#print axioms selectedColumn_lt
#print axioms selectedColumn_injective
#print axioms normalized_chord
#print axioms witness_excluded
#print axioms scaled_block_inverse
end AspisR19.SparseGCoreInverse
