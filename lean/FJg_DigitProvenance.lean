import FJf_PointBody
import FJf_ArraySlots
import FJf_Coordinates
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_DigitProvenance
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)
open FJc_WeightQMBridge (SQ)
abbrev Digit := Array SQ 4#usize

def cell (f : Factors) (k d : Nat) : Option Digit :=
  f.val[k]?.bind (fun row=>row.val[d]?)

def Source (points : Points) (k d : Nat) (digit : Digit) : Prop :=
  ∃ (p : Array SQ 10#usize) (a b f0 f1 f2 f3 : SQ),
    points.val[k]?=some p ∧
    p.val[9-2*FJf_PointIndices.tau d]?=some a ∧
    p.val[8-2*FJf_PointIndices.tau d]?=some b ∧
    FJd_SourceFactor.reference a b=ok [f0,f1,f2,f3] ∧
    digit=Array.make 4#usize [f0,f1,f2,f3]

theorem step (points : Points) (k : Usize) (iter cursor : FIo_RangeNext.Range)
    (factors next : Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0.body points k iter factors=
      ok (.cont (cursor,next))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    (∃ digit,cell next k.val iter.start.val=some digit ∧ Source points k.val iter.start.val digit) ∧
    (∀ j d,j≠k.val ∨ d≠iter.start.val → cell next j d=cell factors j d) := by
  obtain ⟨di,tau,ia,ib,p,a,b,row,back,updated,f0,f1,f2,f3,
    hn,ht,hia,hib,hp,ha,hb,href,hrow,hupdated,hnext⟩ :=
    FJf_PointBody.source points k iter cursor factors next run
  obtain ⟨readRow,eb⟩ := FJf_ArrayOps.index_mut factors k row back hrow
  have hi := (List.getElem_of_getElem? (FJc_ReadSlot.slot _ _ _ readRow)).choose
  have pr := FIo_RangeNext.some_next iter cursor di hn
  have ti := FJf_PointIndices.tau_read di tau ht
  have ci := FJf_Coordinates.indices tau ti.2.1
  rw [eb] at hnext
  subst next
  let digit : Digit := ⟨[f0,f1,f2,f3],rfl⟩
  have slots : ∀ j d,cell (factors.set k updated) j d=
      if k.val=j then (if di.val=d then some digit else row.val[d]?)
      else cell factors j d := by
    intro j d
    unfold cell
    rw [FJf_ArraySlots.set_slot factors k updated hi j]
    by_cases hk : k.val=j
    · rw [if_pos hk,if_pos hk]
      simp only [Option.bind_some]
      exact FJf_ArraySlots.update_slot row updated di _ hupdated d
    · rw [if_neg hk,if_neg hk]
  refine ⟨pr.2.1,pr.2.2.1,pr.2.2.2,?_,?_⟩
  · refine ⟨_,?_,p,a,b,f0,f1,f2,f3,FJc_ReadSlot.slot _ _ _ hp,?_,?_,href,rfl⟩
    · rw [slots,pr.1,if_pos rfl,if_pos rfl]
      rfl
    · have h := FJc_ReadSlot.slot _ _ _ ha
      simpa only [hia,ci.1,ti.2.2,pr.1] using h
    · have h := FJc_ReadSlot.slot _ _ _ hb
      simpa only [hib,ci.2,ti.2.2,pr.1] using h
  · intro j d ne
    rw [slots,pr.1]
    by_cases hk : k.val=j
    · rw [if_pos hk,if_neg (by rcases ne with h|h; exact False.elim (h hk.symm);exact Ne.symm h)]
      unfold cell
      rw [←hk,FJc_ReadSlot.slot _ _ _ readRow]
      rfl
    · rw [if_neg hk]
#print axioms step
end AspisR1.FJg_DigitProvenance
end
