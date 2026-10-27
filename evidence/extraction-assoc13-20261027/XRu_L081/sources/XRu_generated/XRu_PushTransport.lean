import XRu_RowBoth
import XRr_PushExact
import XRo_Join_Carriers
import S7Kani2OwnedPushModel
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRu_PushTransport
abbrev Row := XRu_RowShape.Row
def bw (b : verifier.BatchedWeights) : S7Kani2AccumulatorLoop.BatchedWeights := ⟨b.raw,b.terms⟩
def power (q : aspis_core.field.QM31) : S7Kani2AccumulatorLoop.K :=
 ⟨(q.c0.a,q.c0.b),(q.c1.a,q.c1.b)⟩
/-- Actual row read, arithmetic, mutable writeback and terms commute together.
The concrete reached caller still owes the phase/no-overflow domain. -/
theorem source (b : verifier.BatchedWeights) (i : Usize)
 (q : aspis_core.field.QM31) (m : U32) (bound : i.val<b.raw.length)
 (safe : ∀ row, alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row) b.raw i=ok row →
  ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
   raw.val+(S7Kani2OwnedRow.limb (power q) j).val*m.val<2^64) :
 XRo_Join_Carriers.mapR bw (verifier.BatchedWeights.push b i q m)=
 S7Kani2OwnedPush.push_owned (bw b) i (power q) m := by
 obtain ⟨row,hread,hval⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec b.raw i bound)
 have hr : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row) b.raw i=ok row := hread
 obtain ⟨updated,hu⟩ := S7Kani2OwnedRow.row_total row (power q) m ((b.terms &&& 3#usize)=3#usize) (safe row hr)
 have he := (XRu_RowBoth.source row q m ((b.terms &&& 3#usize)=3#usize) (safe row hr)).trans hu
 have he' : verifier.update_residue_row b.raw.val[i.val] q m ((b.terms &&& 3#usize)=3#usize)=ok updated := by
  rw [←hval]
  exact he
 have emitted := XRr_PushExact.returned b i q m bound updated he'
 have owned := S7Kani2OwnedPushModel.push_of_row (bw b) i (power q) m row updated bound hr hu
 rw [emitted,owned]
 rfl
#print axioms source
end XRu_PushTransport
