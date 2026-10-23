import S6AfterstateDecoderFactoredV1
import S6SourceAfterstateDecodeHelpersV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateFactored.Total
open AspisS6FiveUnrolledCodec

/-- TOTAL final four-field continuation on the full native inputs. Byte length
is a reached source guard; no digest/canonicality/child success is assumed. -/
@[step] theorem part16_spec (bytes : Slice U8)
    (val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 : Array U32 8#usize) (hlen : bytes.length=688) :
    part_16 bytes val1 val3 val5 val7 val9 val11 val13 val15 val17 val19 val21 val23 val25 val27 val29 val31 val33 ⦃ _ => True ⦄ := by
  unfold part_16
  step*

#print axioms part16_spec
end AspisS6SourceCodec.AfterstateFactored.Total
