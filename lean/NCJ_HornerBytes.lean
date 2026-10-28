import NCJ_FieldTotal
import NCJ_HornerInduction
set_option autoImplicit false
noncomputable section
namespace NCJ_HornerBytes
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def Valid (bytes : Slice U8) (i : Usize) : Prop :=
  32*(i.val+1)≤bytes.val.length ∧ ∀ part : Array U8 32#usize,
    part.val=(bytes.val.drop (32*i.val)).take 32 → NCJ_FieldTotal.Canonical part

/-- Literal multiplication/read/add order of the frozen Horner closure. -/
def go (bytes : Slice U8) (x : NE) : List Usize → NE → Result NE
  | [],a => ok a
  | i::is,a => do
    let p ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul a x
    let c ← FIo_Native.weights.field bytes i
    let next ← FIo_Native.aspis_core.field.wide_exact.WideExact.add p c
    go bytes x is next

/-- Total source-ordered Horner carrier construction. Each field validity fact
is on the SAME immutable input slice, and each subsequent state is derived. -/
theorem source (bytes : Slice U8) (x a : NE) (hx : canonE x) (ha : canonE a)
    (is : List Usize) (valid : ∀ i∈is,Valid bytes i) :
    ∃ out,go bytes x is a=ok out ∧ canonE out := by
  induction is generalizing a with
  | nil => exact ⟨a,rfl,ha⟩
  | cons i is ih =>
    obtain ⟨p,hp,cp,_⟩ := LPi_TowerValues.wide_mul a x ha hx
    have hv:=valid i (by simp)
    obtain ⟨part,_,hc,cc⟩ := NCJ_FieldTotal.source bytes i hv.1 hv.2
    obtain ⟨next,hn,cn,_⟩ := NBG_WideCarriers.wide_add p (NCJ_FieldTotal.decode part) cp cc
    obtain ⟨out,run,co⟩ := ih next cn (fun j hj=>valid j (by simp [hj]))
    refine ⟨out,?_,co⟩
    simp only [go,hp,hc,hn,run,bind_tc_ok]

/-- Decoder provenance is retained through the complete list. This is a
source-port result; the adopted polynomial carrier association is separate. -/
theorem exact_coefficients (bytes : Slice U8) (x a : NE) (is : List Usize)
    (coefficients : Usize → NE)
    (reads : ∀ i∈is,FIo_Native.weights.field bytes i=ok (coefficients i)) :
    go bytes x is a=NCJ_HornerInduction.go x (is.map coefficients) a := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih =>
    simp only [go,List.map_cons,NCJ_HornerInduction.go,NCJ_HornerInduction.step,bind_assoc_eq]
    rw [reads i (by simp)]
    simp only [bind_tc_ok]
    congr 1
    funext product
    congr 1
    funext next
    exact ih next (fun j hj=>reads j (by simp [hj]))

#print axioms source
#print axioms exact_coefficients
end NCJ_HornerBytes
