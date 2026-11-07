import PCG_HelperRef.Funs
import PCB_SmallStatementLaws
import PCB_Location
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_PageLaws
abbrev Page := PCB_SmallStatementRef.pool_v1.root_history.RootHistoryPageV1

theorem full_scalar (filled : U16) :
 PCG_HelperRef.full filled = ok (decide (filled.val = 256)) := by
 by_cases h : filled.val = 256
 · have hc : core.convert.num.FromUsizeU16.from filled = 256#usize := by scalar_tac
   simp [PCG_HelperRef.full,lift,pure,bind_tc_ok,hc,h]
 · have hc : core.convert.num.FromUsizeU16.from filled ≠ 256#usize := by scalar_tac
   simp [PCG_HelperRef.full,lift,pure,bind_tc_ok,hc,h]

theorem row_242 (page : Page) :
 (PCG_HelperRef.full page.filled,page) = (ok (decide (page.filled.val = 256)),page) := by
 rw [full_scalar]

def slot (sequence : U64) : Usize :=
 Usize.ofNatCore (sequence.val % 256) (by
  have h : sequence.val % 256 < 256 := Nat.mod_lt _ (by decide)
  scalar_tac)

def modelIndex (page : U64) (filled : U16) (sequence : U64) : Option Usize :=
 if sequence.val / 256 = page.val ∧ sequence.val % 256 < filled.val
 then some (slot sequence) else none

theorem index_result (page : U64) (filled : U16) (sequence : U64) :
 PCG_HelperRef.get_index page filled sequence = ok (modelIndex page filled sequence) := by
 obtain ⟨q,hq,vq⟩ := UScalar.div_spec (x:=sequence) (y:=256#u64) (by decide)
 obtain ⟨r,hr,vr⟩ := WP.spec_imp_exists
  (UScalar.rem_spec (x:=sequence) (y:=256#u64) (by decide))
 have vqNat : q.val = sequence.val / 256 := by simpa using vq
 have vrNat : r.val = sequence.val % 256 := by simpa using vr
 have rmod : r.val % 65536 = r.val := Nat.mod_eq_of_lt (by have h := Nat.mod_lt sequence.val (by decide : 0 < 256); omega)
 have small : r.val < 256 := by simpa using (vr ▸ Nat.mod_lt sequence.val (by decide))
 have castval : (UScalar.cast .U16 r).val = r.val := by scalar_tac
 by_cases hp : sequence.val / 256 = page.val
 · have eqpage : q = page := by scalar_tac
   by_cases hs : sequence.val % 256 < filled.val
   · have ltfilled : ¬ UScalar.cast .U16 r >= filled := by scalar_tac
     simp only [PCG_HelperRef.get_index,hq,hr,lift,bind_tc_ok]
     simp only [eqpage,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,if_false]
     simp [ltfilled,modelIndex,hp,hs]
     apply UScalar.eq_of_val_eq
     simp only [slot]
     scalar_tac
   · have gefilled : UScalar.cast .U16 r >= filled := by scalar_tac
     simp [PCG_HelperRef.get_index,hq,hr,lift,pure,bind_tc_ok,eqpage,gefilled,rmod,castval,modelIndex,hp,hs] <;> scalar_tac
 · have nepage : q ≠ page := by scalar_tac
   simp [PCG_HelperRef.get_index,hq,hr,lift,pure,bind_tc_ok,nepage,rmod,castval,modelIndex,hp] <;> scalar_tac

def borrowed (page : Page) (sequence : U64) := do
 let index ← PCG_HelperRef.get_index page.page_number page.filled sequence
 ok (match index with
  | none => none
  | some i => page.roots.val[i.val]?)

/-- Complete returned place/value and unchanged receiver. The native y-prime
certificate identifies the returned loan with this SAME roots slot. -/
theorem row_241 (page : Page) (sequence : U64) :
 (borrowed page sequence,page) =
 (ok (if sequence.val / 256 = page.page_number.val ∧ sequence.val % 256 < page.filled.val
   then page.roots.val[sequence.val % 256]? else none),page) := by
 simp only [borrowed,index_result,bind_tc_ok,modelIndex]
 by_cases h : sequence.val / 256 = page.page_number.val ∧ sequence.val % 256 < page.filled.val
 · simp only [if_pos h] <;> rfl
 · simp only [if_neg h] <;> rfl

theorem in_range (page : Page) (sequence : U64) :
 sequence.val % 256 < page.roots.val.length := by
 have h := page.roots.property
 change page.roots.val.length = 256 at h
 rw [h]
 exact Nat.mod_lt _ (by decide)

#print axioms full_scalar
#print axioms row_242
#print axioms index_result
#print axioms row_241
#print axioms in_range
end PCG_PageLaws
