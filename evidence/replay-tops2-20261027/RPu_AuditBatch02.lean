import Lean
import RPu_FJo_OpeningDecodes
import RPu_FJo_QueryInjective
import RPu_FJl_PackedSelected
import RPu_FJl_PackedInjective
import RPu_FJl_PackedInitial
import RPu_FJo_PackedLeaves
import RPu_FJo_FourLiteral
import RPu_FJi_FourValue
import RPu_FJi_ArrayAdapter
import RPu_FJo_AdaptedDots
import RPu_FJo_PackedDecodes
import RPu_FJi_MatchingMeaning
import RPu_FJi_QueryJoin
import RPu_FJl_OpeningBytes
import RPu_FJo_ActualOpening
import RPu_FJl_WordRead
import RPu_FJl_LiteralW
import RPu_FJl_WordLane
import RPu_FJl_WordTails
import RPu_FJo_Sum29
import RPu_FJo_ColumnSum
import RPu_FJo_BatchedWord
import RPu_FJo_BatchedFormula
import RPu_FJo_DotsBatched
import RPu_FJo_QueryBatched
import RPu_FJl_Observation
import RPu_FJo_QueryRaw
import RPu_FJo_PhaseSame
import RPu_Port5Q1_CircleObservation
import RPu_FJo_FoldedSelected
import RPu_FJo_CircleInverses
import RPu_FJp_CircleTransport
import RPu_FJp_MatchingJoin
import RPu_FJp_LiteralJoin
import RPu_FJp_SourceValues
import RPu_FJp_Query00
import RPu_FJp_Query01
import RPu_FJp_Query02
import RPu_FJp_Query03
import RPu_FJp_Query04
import RPu_FJp_Query05
import RPu_FJp_Query06
import RPu_FJp_Query07
import RPu_FJp_Query08
import RPu_FJp_Query09
import RPu_FJp_Query10
import RPu_FJp_Query11
import RPu_FJp_Query12
import RPu_FJp_Query13
import RPu_FJp_Query14
import RPu_FJp_Query15
import RPu_FJp_Query16
import RPu_FJp_Query17
import RPu_FJp_Query18
import RPu_FJp_Query19
import RPu_FJp_Query20
import RPu_FJp_Query21
import RPu_FJp_ObservedMatch
import RPu_FJo_BodySlice
import RPu_FJo_BodyGamma
import RPu_FJo_WriterGamma
import RPu_FJi_SelectedPowers
import RPu_FJl_PowersCanonical
import RPu_FJl_ReaderCanonical
import RPu_FJo_ReaderGamma
import RPu_FJo_GammaPersistence
import RPu_FJi_Query00
import RPu_FJi_Query01
import RPu_FJi_Query02
import RPu_FJi_Query03
import RPu_FJi_Query04
import RPu_FJi_Query05
import RPu_FJi_Query06
import RPu_FJi_Query07
import RPu_FJi_Query08
import RPu_FJi_Query09
import RPu_FJi_Query10
import RPu_FJi_Query11
import RPu_FJi_Query12
import RPu_FJi_Query13
import RPu_FJi_Query14
import RPu_FJi_Query15
import RPu_FJi_Query16
import RPu_FJi_Query17
import RPu_FJi_Query18
import RPu_FJi_Query19
import RPu_FJi_Query20
import RPu_FJi_Query21
import RPu_FJi_AllQueries
import RPu_FJl_ReaderPowers
import RPu_FJo_ReaderLiteralPowers
import RPu_FJo_Tx1Scratch
import RPu_FJo_SourceCoordinate
import RPu_FJo_SourceArray
import RPu_FJo_Tx1Powers
import RPu_FJl_PreparedGamma
import RPu_FJl_PreparedAlpha
import RPu_FJl_PreparedAtValues
import RPu_FJo_Tx1AtPowers
import RPu_FJo_Tx1GammaCanonical
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPu_FJo_OpeningDecodes, `RPu_FJo_QueryInjective, `RPu_FJl_PackedSelected, `RPu_FJl_PackedInjective, `RPu_FJl_PackedInitial, `RPu_FJo_PackedLeaves, `RPu_FJo_FourLiteral, `RPu_FJi_FourValue, `RPu_FJi_ArrayAdapter, `RPu_FJo_AdaptedDots, `RPu_FJo_PackedDecodes, `RPu_FJi_MatchingMeaning, `RPu_FJi_QueryJoin, `RPu_FJl_OpeningBytes, `RPu_FJo_ActualOpening, `RPu_FJl_WordRead, `RPu_FJl_LiteralW, `RPu_FJl_WordLane, `RPu_FJl_WordTails, `RPu_FJo_Sum29, `RPu_FJo_ColumnSum, `RPu_FJo_BatchedWord, `RPu_FJo_BatchedFormula, `RPu_FJo_DotsBatched, `RPu_FJo_QueryBatched, `RPu_FJl_Observation, `RPu_FJo_QueryRaw, `RPu_FJo_PhaseSame, `RPu_Port5Q1_CircleObservation, `RPu_FJo_FoldedSelected, `RPu_FJo_CircleInverses, `RPu_FJp_CircleTransport, `RPu_FJp_MatchingJoin, `RPu_FJp_LiteralJoin, `RPu_FJp_SourceValues, `RPu_FJp_Query00, `RPu_FJp_Query01, `RPu_FJp_Query02, `RPu_FJp_Query03, `RPu_FJp_Query04, `RPu_FJp_Query05, `RPu_FJp_Query06, `RPu_FJp_Query07, `RPu_FJp_Query08, `RPu_FJp_Query09, `RPu_FJp_Query10, `RPu_FJp_Query11, `RPu_FJp_Query12, `RPu_FJp_Query13, `RPu_FJp_Query14, `RPu_FJp_Query15, `RPu_FJp_Query16, `RPu_FJp_Query17, `RPu_FJp_Query18, `RPu_FJp_Query19, `RPu_FJp_Query20, `RPu_FJp_Query21, `RPu_FJp_ObservedMatch, `RPu_FJo_BodySlice, `RPu_FJo_BodyGamma, `RPu_FJo_WriterGamma, `RPu_FJi_SelectedPowers, `RPu_FJl_PowersCanonical, `RPu_FJl_ReaderCanonical, `RPu_FJo_ReaderGamma, `RPu_FJo_GammaPersistence, `RPu_FJi_Query00, `RPu_FJi_Query01, `RPu_FJi_Query02, `RPu_FJi_Query03, `RPu_FJi_Query04, `RPu_FJi_Query05, `RPu_FJi_Query06, `RPu_FJi_Query07, `RPu_FJi_Query08, `RPu_FJi_Query09, `RPu_FJi_Query10, `RPu_FJi_Query11, `RPu_FJi_Query12, `RPu_FJi_Query13, `RPu_FJi_Query14, `RPu_FJi_Query15, `RPu_FJi_Query16, `RPu_FJi_Query17, `RPu_FJi_Query18, `RPu_FJi_Query19, `RPu_FJi_Query20, `RPu_FJi_Query21, `RPu_FJi_AllQueries, `RPu_FJl_ReaderPowers, `RPu_FJo_ReaderLiteralPowers, `RPu_FJo_Tx1Scratch, `RPu_FJo_SourceCoordinate, `RPu_FJo_SourceArray, `RPu_FJo_Tx1Powers, `RPu_FJl_PreparedGamma, `RPu_FJl_PreparedAlpha, `RPu_FJl_PreparedAtValues, `RPu_FJo_Tx1AtPowers, `RPu_FJo_Tx1GammaCanonical ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPU_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPU_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPU_AUDIT_COMPLETE declarations={count} modules={selected.size}"
