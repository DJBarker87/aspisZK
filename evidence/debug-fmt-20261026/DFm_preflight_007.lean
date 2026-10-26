import Lean
import ExtractedPrefixFieldAgreement
import ExtractedPrefixParseCore
import ExtractedPrefixRecordStep
import ExtractedRecordFraming
import ExtractedRecordHighZero
import ExtractedRecordLimbCanonicality
import ExtractedPrefixHeaderBytes
import ExtractedPrefixLoopMap
import ExtractedPrefixTrace
import ExtractedPrefixTypedFullCurrent
import ExtractedRecordByteCanonicality
import ExtractedRecordStrictCodec
import ExtractedRecordValidator
import RecordPayloadPartition
import S1SemanticPrefixModelV1
import ExtractedPrefixChunkOrder
import ExtractedPrefixParse
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `ExtractedPrefixFieldAgreement, `ExtractedPrefixParseCore, `ExtractedPrefixRecordStep, `ExtractedRecordFraming, `ExtractedRecordHighZero, `ExtractedRecordLimbCanonicality, `ExtractedPrefixHeaderBytes, `ExtractedPrefixLoopMap, `ExtractedPrefixTrace, `ExtractedPrefixTypedFullCurrent, `ExtractedRecordByteCanonicality, `ExtractedRecordStrictCodec, `ExtractedRecordValidator, `RecordPayloadPartition, `S1SemanticPrefixModelV1, `ExtractedPrefixChunkOrder, `ExtractedPrefixParse ]
  let mut rows : Array Json := #[]
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let value := c.value? true
        let refs := c.type.getUsedConstants ++ (value.map Expr.getUsedConstants |>.getD #[])
        let axs ← collectAxioms n
        rows := rows.push (Json.mkObj [
          ("module", toJson owner.toString), ("name", toJson n.toString),
          ("type", toJson (reprStr c.type)), ("value", toJson (reprStr value)),
          ("levelParams", toJson (reprStr c.levelParams)),
          ("hints", toJson (match c.hints with | .opaque => "opaque" | .abbrev => "abbrev" | .regular h => s!"regular {h}")), ("unsafe", toJson c.isUnsafe),
          ("axiom", toJson c.isAxiom), ("refs", toJson (refs.map Name.toString)),
          ("axioms", toJson (axs.map Name.toString))])
        elabCommand (← `(#print axioms $(mkIdent n)))
  liftIO <| IO.FS.writeFile "DFm_importers-before.json" (Json.arr rows).compress
  logInfo m!"DFM_AUDIT_COMPLETE declarations={rows.size}"
