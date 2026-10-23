import S6AfterstateDecoderPart4TotalV1
import S6SourceAfterstateDecodeHelpersV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateFactored.Total
open AspisS6FiveUnrolledCodec

/-- TOTAL four-field continuation on the full native inputs. Byte length
is a reached source guard; no digest/canonicality/child success is assumed. -/
@[step] theorem part0_spec (bytes : Slice U8)
    (val1 : Array U32 8#usize) (hlen : bytes.length=688) :
    part_0 bytes val1 ⦃ _ => True ⦄ := by
  unfold part_0
  step*

#print axioms part0_spec
end AspisS6SourceCodec.AfterstateFactored.Total
