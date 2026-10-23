import S6SourceAgreementPart11V1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6SourceCodec.Agreement

theorem encode_eq (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    AspisS6SourceCodec.encode = AspisS6FiveUnrolledCodec.StdOptions.encode unused := by
  exact Links.link_235 unused

#print axioms encode_eq

theorem decode_eq (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :
    AspisS6SourceCodec.decode = AspisS6FiveUnrolledCodec.StdOptions.decode unused := by
  exact Links.link_236 unused

#print axioms decode_eq

end AspisS6SourceCodec.Agreement
