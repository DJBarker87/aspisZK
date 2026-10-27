import LPn_ClaimsTrace
open Aeneas Aeneas.Std Result LPl_Kit_Release
set_option autoImplicit false
namespace LPn.Claims
open LPn.ClaimsModel

theorem bound25 (p : r1_wire.Prefix) : 25 < p.records.val.length := by
  have size := p.records.property
  change p.records.val.length=27 at size
  omega

def framed (p : r1_wire.Prefix) : Slice U8 := p.records.val[25]'(bound25 p)
def record (p : r1_wire.Prefix) : r1_wire.ValidatedRecord := ⟨25#u8,framed p⟩

theorem read25 (p : r1_wire.Prefix) :
    Array.index_usize p.records 25#usize = ok (framed p) := by
  have index : (25#usize).val=25 := by norm_num [UScalar.ofNatCore_val_eq]
  rw [Array.index_usize,Array.getElem?_Usize_eq,index,List.getElem?_eq_getElem (bound25 p)]
  rfl

theorem native_result (reserved : Bool) (p : r1_wire.Prefix) (after : State)
    (trace : Trace (record p) 3 after) :
    owned reserved p = if reserved then LPn.ClaimsModel.finish after else ok (.Err .Allocation) :=
  allocated_result reserved p (framed p) after (read25 p) trace

theorem native_success (p : r1_wire.Prefix) (rows : List Row)
    (trace : Trace (record p) 3 (.Ok rows)) :
    ∃ h : rows.length=(3#usize).val,
      r1_semantic.claims p = ok (.Ok (⟨rows,h⟩ : Array Row 3#usize)) := by
  have size := success_length (record p) 3 rows trace
  have model := prefix_result p (framed p) (.Ok rows) (read25 p) trace
  refine ⟨size,?_⟩
  simpa [LPn.ClaimsModel.finish,size] using model

theorem native_error (p : r1_wire.Prefix) (e : r1_wire.Error)
    (trace : Trace (record p) 3 (.Err e)) :
    r1_semantic.claims p = ok (.Err e) := by
  exact prefix_result p (framed p) (.Err e) (read25 p) trace

/-- All rejected allocations are explicit native rejections, not successful
    cohort executions; no malloc-success precondition enters the caller. -/
theorem allocation_rejection (p : r1_wire.Prefix) :
    owned false p = ok (.Err .Allocation) := rfl

theorem point_domain (point lane : Nat) (p : r1_wire.Prefix)
    (hp : point<3) (hl : lane<29) : point*29+lane<87 ∧ point*29+lane<116 := by omega

#print axioms bound25
#print axioms read25
#print axioms native_result
#print axioms native_success
#print axioms native_error
#print axioms allocation_rejection
#print axioms point_domain
end LPn.Claims
