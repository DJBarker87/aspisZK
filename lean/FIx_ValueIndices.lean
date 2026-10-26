import FIw_WordValue
set_option autoImplicit false
namespace AspisR1.FIx_ValueIndices
open Aeneas Aeneas.Std Result

theorem inc (i next : Usize) (run : i+1#usize=ok next) : next.val=i.val+1 :=
  FIw_WordValue.add i 1#usize next run

theorem offset (base i out : Usize) (run : base+i=ok out) : out.val=base.val+i.val :=
  FIw_WordValue.add base i out run

theorem bound (base i out : Usize) (hb : base.val≤20) (hi : i.val<10)
    (value : out.val=base.val+i.val) : out.val<(33#usize).val := by
  rw [value]
  change base.val+i.val<33
  omega
#print axioms inc
#print axioms offset
#print axioms bound
end AspisR1.FIx_ValueIndices
