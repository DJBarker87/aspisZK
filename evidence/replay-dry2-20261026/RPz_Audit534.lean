import Lean
import AspisFormal.V5FriConcreteEncoderApplicability
import AspisFormal.V5FriInitialCircleEncoderIdentity
import AspisFormal.V6OneFoldCandidateExtraction
import AspisFormal.V6EncoderDistance
import AspisFormal.V7ExactOneFoldDomains
import R1FixedWidthDecoder
import R1FixedWidthSlice
import R1FixedWidthEncoding

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `AspisFormal.V5FriConcreteEncoderApplicability, `AspisFormal.V5FriInitialCircleEncoderIdentity, `AspisFormal.V6OneFoldCandidateExtraction, `AspisFormal.V6EncoderDistance, `AspisFormal.V7ExactOneFoldDomains, `R1FixedWidthDecoder, `R1FixedWidthSlice, `R1FixedWidthEncoding ]
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
