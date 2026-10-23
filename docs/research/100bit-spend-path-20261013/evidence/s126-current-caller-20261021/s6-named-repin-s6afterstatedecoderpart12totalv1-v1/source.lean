import S6AfterstateDecoderPart16TotalV1
import S6SourceAfterstateDecodeHelpersV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateFactored.Total
open AspisS6FiveUnrolledCodec

/-- TOTAL four-field continuation on the full native inputs. Byte length
is a reached source guard; no digest/canonicality/child success is assumed. -/
@[step] theorem part12_spec (bytes : Slice U8)
    (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 : Array U32 8#usize) (hlen : bytes.length=688) :
    part_12 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 ⦃ _ => True ⦄ := by
  unfold part_12
  step*

#print axioms part12_spec
end AspisS6SourceCodec.AfterstateFactored.Total
