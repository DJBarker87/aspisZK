import Lean
import S6StdByteSliceEqualityV1
import S6SourceCanonicalTotalV1
import S6SourceSnapshotValidatorTotalV1
import S6SourceAfterstateValidatorTotalV1
import S6SourceAfterstateDecodeHelpersV1
import S6AfterstateDecoderPart16TotalV1
import S6AfterstateDecoderPart12TotalV1
import S6AfterstateDecoderPart8TotalV1

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `S6StdByteSliceEqualityV1, `S6SourceCanonicalTotalV1, `S6SourceSnapshotValidatorTotalV1, `S6SourceAfterstateValidatorTotalV1, `S6SourceAfterstateDecodeHelpersV1, `S6AfterstateDecoderPart16TotalV1, `S6AfterstateDecoderPart12TotalV1, `S6AfterstateDecoderPart8TotalV1 ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let axs ← collectAxioms n
        logInfo m!"RPZ_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ_AUDIT_COMPLETE declarations={count} modules={selected.size}"
