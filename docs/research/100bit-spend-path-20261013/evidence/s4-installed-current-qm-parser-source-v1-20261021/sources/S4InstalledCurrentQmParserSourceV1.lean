import FourDotsCurrentQmParserRootV1
import S4ConcreteTailInstallRootV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1FastDotsInstalledCurrentQmParserSourceV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Aeneas.Std.U8

/-- The concrete installed parser slot equals the transparent actual generated
QM31 decoder followed by its checked carrier rewrap, for every slice and every
Result/Option outcome. -/
theorem installed_parser_is_actual_source (base : Ops) (bytes : Slice U8) :
    (AspisR1FastDotsConcreteTailInstallRootV1.install base).qm31FromBytes bytes =
      AspisR1FastDotsCurrentQmParserRootV1.mapResult
        (Option.map AspisR1FastDotsCurrentQmParserRootV1.toCurrent)
        (AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes) := by
  have hs := AspisR1FastDotsConcreteTailInstallRootV1.source_bindings base
  rw [hs.2.2.2.1]
  rfl

/-- On the exact sixteen-byte frames passed to the callback parser, the same
installed slot is the retained strict decoder. In particular its `none`
branch rejects noncanonical coordinates; no accepted-only premise is used. -/
theorem installed_parser_fixed16_strict (base : Ops) (bytes : Array U8 16#usize) :
    (AspisR1FastDotsConcreteTailInstallRootV1.install base).qm31FromBytes
        (Array.to_slice bytes) =
      .ok ((AspisR1.RetainedFieldByteCodec.decodeQM31LE
        (AspisR1.CandidateParserByteOrder.arrayBytes16 bytes)).map
        AspisR1FastDotsCurrentQmParserRootV1.limbsToCurrent) := by
  have hs := AspisR1FastDotsConcreteTailInstallRootV1.source_bindings base
  rw [hs.2.2.2.1]
  exact AspisR1FastDotsCurrentQmParserRootV1.parser_fixed_total bytes

#print axioms installed_parser_is_actual_source
#print axioms installed_parser_fixed16_strict

end AspisR1FastDotsInstalledCurrentQmParserSourceV1
