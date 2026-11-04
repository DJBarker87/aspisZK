import NGO_AtDomain
import NGO_CallerDomains
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_SourceDomain
/-- Every record window supplied by the original parse_record_at get has
exactly the framed length used by ALL deployed decode_k call shapes. -/
theorem caller (bytes framed : Slice U8) (row tag : U8) (size offset finish N off start : Usize)
    (call : NGO_CallerDomains.Call row.val N.val off.val)
    (shape : NGD_AtG.shape row=ok (some (tag,size)))
    (get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=offset,«end»:=finish}=ok (some framed))
    (addition : finish.val=offset.val+5+size.val)
    (startValue : start.val=32*off.val) :
    NGD_DecodeTrace.Domain N
      ({row,framed} : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord) off start ∧
      ¬row<14#u8 := by
  have numeric:=NGO_CallerDomains.numeric row.val N.val off.val call
  have sizeValue:=NGD_RowPayload.exact_size row tag size numeric.2.1 shape
  have source:=NGO_AtDomain.from_source_window bytes framed offset finish size get addition
  apply NGO_CallerDomains.record_domain N off start _ call _ startValue
  simpa only [sizeValue] using source.1
#print axioms caller
end NGO_SourceDomain
