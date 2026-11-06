import NJB_Words
import NJB_MaskTable
set_option autoImplicit false
namespace AspisR1.NJB_Cuts
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
structure Event where
 operation : Nat
 left : NQ
 right : NQ
/-- Transcription of NJB_residual's operand/kind assertions, with the final
native result exactly the last logged reply. No callee success or model
endpoint equation occurs in this predicate. NJB_CUTS.md pins the harness. -/
def residualLeft (a : Fin 10 → NQ) (r : Fin 17 → NQ) (j : Fin 17) : NQ :=
 ![a 9,a 9,a 9,a 9,r 0,r 2,a 4,a 5,r 6,a 6,a 7,r 9,a 8,r 12,r 4,r 5,r 14] j
def residualRight (a : Fin 10 → NQ) (r : Fin 17 → NQ) (j : Fin 17) : NQ :=
 ![a 0,a 1,a 2,a 3,r 1,r 3,r 1,r 0,r 7,r 3,r 2,r 10,r 5,r 11,r 13,r 8,r 15] j
def residualKind (j : Fin 17) : Nat := ![2,2,2,2,0,0,0,0,1,0,0,1,0,1,0,0,2] j
def residual (a : Fin 10 → NQ) (r : Fin 17 → NQ) (events : Fin 17 → Event)
 (calls : Nat) (out : NQ) : Prop :=
 (∀ i,Canon (a i)) ∧ (∀ i,Canon (r i)) ∧ calls=17 ∧ out=r 16 ∧
 ∀ j,(events j).operation=residualKind j ∧ (events j).left=residualLeft a r j ∧
 (events j).right=residualRight a r j
/-- Transcription of the arbitrary-prestate high native iteration. Only the
selected input and reply are constrained canonical; every other cell is framed. -/
def high (source : Fin 64 → NQ) (before after : Fin 7 → NQ) (b : Fin 64)
 (reply : NQ) (e : Event) (calls next : Nat) : Prop :=
 let c := R0P.activeMaskCoordinate (NJB_MaskTable.nativeMasks b)
 Canon (before c) ∧ Canon (source b) ∧ Canon reply ∧ calls=1 ∧ next=b.val+1 ∧
 e.operation=1 ∧ e.left=before c ∧ e.right=source b ∧
 ∀ i,after i=if c=i then reply else before i
/-- Finite low-window index table copied from the native assertions. -/
def lowIndices (c : Fin 7) : List (Fin 16) :=
 match c.val with
 | 0=>[11,12] | 1=>[0,11,12] | 2=>[0,12] | 3=>[11] | 4=>[0,11]
 | 5=>[1,2,5,6,9,10,13,14] | _=>[0,2,4,6,7,9,10]
def lowCount (c : Fin 7) : Nat := ![2,3,2,1,2,8,7] c
theorem low_count_positive (c : Fin 7) : 0<lowCount c := by fin_cases c <;> decide
theorem low_count_bound (c : Fin 7) : lowCount c≤8 := by fin_cases c <;> decide
def lowIndex (c : Fin 7) (j : Nat) : Fin 16 := ((lowIndices c)[j]?).getD 0
def lowLeft (high : Fin 7 → NQ) (low : Fin 16 → NQ) (sum : NQ) (r : Fin 17 → NQ)
 (c : Fin 7) (j : Fin (lowCount c+1)) : NQ :=
 if j.val<lowCount c-1 then
  if j.val=0 then low (lowIndex c 0) else r ⟨j.val-1,by have := low_count_bound c;omega⟩
 else if j.val=lowCount c-1 then high c else sum
def lowRight (low : Fin 16 → NQ) (r : Fin 17 → NQ) (c : Fin 7)
 (j : Fin (lowCount c+1)) : NQ :=
 if j.val<lowCount c-1 then low (lowIndex c (j.val+1))
 else if j.val=lowCount c-1 then
  if lowCount c=1 then low (lowIndex c 0) else r ⟨lowCount c-2,by have := low_count_bound c;omega⟩
 else r ⟨lowCount c-1,by have := low_count_bound c;omega⟩
/-- Exact low-window assertion transcription. Unentered log slots are not
constrained as output observations. Canonical ghost replies in unused input
slots can be instantiated with the proved canonical ZERO by the root. -/
def low (high : Fin 7 → NQ) (low : Fin 16 → NQ) (sum : NQ) (r : Fin 17 → NQ)
 (c : Fin 7) (events : Fin (lowCount c+1) → Event) (calls next : Nat) (out : NQ) : Prop :=
 (∀ i,Canon (high i)) ∧ (∀ i,Canon (low i)) ∧ Canon sum ∧ (∀ i,Canon (r i)) ∧
 calls=lowCount c+1 ∧ next=c.val+1 ∧
 out=r ⟨lowCount c,by have := low_count_bound c;omega⟩ ∧
 ∀ j,(events j).operation=(if j.val=lowCount c-1 then 0 else 1) ∧
 (events j).left=lowLeft high low sum r c j ∧ (events j).right=lowRight low r c j
#print axioms low_count_positive
#print axioms low_count_bound
/-- Native control counters are bounded on the complete caller domain. -/
theorem high_next_bound (b : Fin 64) : b.val+1≤64 := by omega
theorem low_next_bound (c : Fin 7) : c.val+1≤7 := by omega
#print axioms high_next_bound
#print axioms low_next_bound
end AspisR1.NJB_Cuts
