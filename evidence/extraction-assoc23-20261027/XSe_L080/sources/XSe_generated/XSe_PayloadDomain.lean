import XSe_RecordDomain
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_PayloadDomain
/-- The actual header geometry and slice call establish the CLOSED native
validator's entire payload domain. These are prefix cuts, not validity claims. -/
theorem source (row tag : U8) (size total : Usize) (record payload : Slice U8)
 (shape : r1_wire.row_shape row=ok (some (tag,size)))
 (add : (5#usize+size : Result Usize)=ok total)
 (length : Slice.len record=total)
 (selected : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
  record {start:=5#usize}=ok payload) : payload.val.length≤3712 := by
 have bound := XSe_RecordDomain.source row tag size shape
 let full : Usize := UScalar.ofNat (5+size.val) (by change 5+size.val≤4294967295;omega)
 have hfull : (5#usize+size : Result Usize)=ok full := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
 have same := Result.ok.inj (add.symm.trans hfull)
 subst total
 have recordLength : record.val.length=5+size.val := by scalar_tac
 change (if (5#usize).val≤record.length then ok (record.drop 5#usize) else fail .undef)=ok payload at selected
 split at selected
 · cases Result.ok.inj selected
   change (record.val.drop (5#usize).val).length≤3712
   rw [List.length_drop,recordLength]
   change 5+size.val-5≤3712
   omega
 · cases selected
#print axioms source
end XSe_PayloadDomain
