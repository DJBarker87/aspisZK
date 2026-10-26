import Lean
import R17TableAChunk01Certificate
import R17NarrowFunsA01ChunkPower
import R17ActualA01IndexPower
import R17TableAChunk02Certificate
import R17NarrowFunsA02ChunkPower
import R17ActualA02IndexPower
import R17TableAChunk03Certificate
import R17NarrowFunsA03ChunkPower
import R17ActualA03IndexPower
import R17TableAChunk04Certificate
import R17NarrowFunsA04ChunkPower
import R17ActualA04IndexPower
import R17TableAChunk05Certificate
import R17NarrowFunsA05ChunkPower
import R17ActualA05IndexPower
import R17TableAChunk06Certificate
import R17NarrowFunsA06ChunkPower
import R17ActualA06IndexPower
import R17TableAChunk07Certificate
import R17NarrowFunsA07ChunkPower
import R17ActualA07IndexPower
import R17TableAChunk08Certificate
import R17NarrowFunsA08ChunkPower
import R17ActualA08IndexPower
import R17TableAChunk09Certificate
import R17NarrowFunsA09ChunkPower
import R17ActualA09IndexPower
import R17TableAChunk10Certificate
import R17NarrowFunsA10ChunkPower
import R17ActualA10IndexPower
import R17TableAChunk11Certificate
import R17NarrowFunsA11ChunkPower
import R17ActualA11IndexPower
import R17TableAChunk12Certificate
import R17NarrowFunsA12ChunkPower
import R17ActualA12IndexPower
import R17TableAChunk13Certificate
import R17NarrowFunsA13ChunkPower
import R17ActualA13IndexPower
import R17TableAChunk14Certificate
import R17NarrowFunsA14ChunkPower
import R17ActualA14IndexPower
import R17TableAChunk15Certificate
import R17NarrowFunsA15ChunkPower
import R17ActualA15IndexPower
import R17TableBChunk00Certificate
import R17NarrowFunsB00ChunkPower
import R17ActualB00IndexPower
import R17TableBChunk01Certificate
import R17NarrowFunsB01ChunkPower
import R17ActualB01IndexPower
import R17TableBChunk02Certificate
import R17NarrowFunsB02ChunkPower
import R17ActualB02IndexPower
import R17TableBChunk03Certificate
import R17NarrowFunsB03ChunkPower
import R17ActualB03IndexPower
import R17TableBChunk04Certificate
import R17NarrowFunsB04ChunkPower
import R17ActualB04IndexPower
import R17TableBChunk05Certificate
import R17NarrowFunsB05ChunkPower
import R17ActualB05IndexPower
import R17TableBChunk06Certificate
import R17NarrowFunsB06ChunkPower
import R17ActualB06IndexPower
import R17TableBChunk07Certificate
import R17NarrowFunsB07ChunkPower
import R17ActualB07IndexPower
import R17TableBChunk08Certificate
import R17NarrowFunsB08ChunkPower
import R17ActualB08IndexPower
import R17TableBChunk09Certificate
import R17NarrowFunsB09ChunkPower
import R17ActualB09IndexPower
import R17TableBChunk10Certificate
import R17NarrowFunsB10ChunkPower
import R17ActualB10IndexPower
import R17TableBChunk11Certificate
import R17NarrowFunsB11ChunkPower
import R17ActualB11IndexPower
import R17TableBChunk12Certificate
import R17NarrowFunsB12ChunkPower
import R17ActualB12IndexPower
import R17TableBChunk13Certificate
import R17NarrowFunsB13ChunkPower
import R17ActualB13IndexPower
import R17TableBChunk14Certificate
import R17NarrowFunsB14ChunkPower
import R17ActualB14IndexPower
import R17TableBChunk15Certificate
import R17NarrowFunsB15ChunkPower
import R17ActualB15IndexPower
import R17ZPowAddition
import R17ActualWholeTablePower
import R17CircleCoordinateMulBridge
import R17CircleCoordinatePowerBridge
import R17TableCirclePowerBridge
import R17FibrePointStoredDomain
import R17FibrePointActualSuccess

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R17TableAChunk01Certificate, `R17NarrowFunsA01ChunkPower, `R17ActualA01IndexPower, `R17TableAChunk02Certificate, `R17NarrowFunsA02ChunkPower, `R17ActualA02IndexPower, `R17TableAChunk03Certificate, `R17NarrowFunsA03ChunkPower, `R17ActualA03IndexPower, `R17TableAChunk04Certificate, `R17NarrowFunsA04ChunkPower, `R17ActualA04IndexPower, `R17TableAChunk05Certificate, `R17NarrowFunsA05ChunkPower, `R17ActualA05IndexPower, `R17TableAChunk06Certificate, `R17NarrowFunsA06ChunkPower, `R17ActualA06IndexPower, `R17TableAChunk07Certificate, `R17NarrowFunsA07ChunkPower, `R17ActualA07IndexPower, `R17TableAChunk08Certificate, `R17NarrowFunsA08ChunkPower, `R17ActualA08IndexPower, `R17TableAChunk09Certificate, `R17NarrowFunsA09ChunkPower, `R17ActualA09IndexPower, `R17TableAChunk10Certificate, `R17NarrowFunsA10ChunkPower, `R17ActualA10IndexPower, `R17TableAChunk11Certificate, `R17NarrowFunsA11ChunkPower, `R17ActualA11IndexPower, `R17TableAChunk12Certificate, `R17NarrowFunsA12ChunkPower, `R17ActualA12IndexPower, `R17TableAChunk13Certificate, `R17NarrowFunsA13ChunkPower, `R17ActualA13IndexPower, `R17TableAChunk14Certificate, `R17NarrowFunsA14ChunkPower, `R17ActualA14IndexPower, `R17TableAChunk15Certificate, `R17NarrowFunsA15ChunkPower, `R17ActualA15IndexPower, `R17TableBChunk00Certificate, `R17NarrowFunsB00ChunkPower, `R17ActualB00IndexPower, `R17TableBChunk01Certificate, `R17NarrowFunsB01ChunkPower, `R17ActualB01IndexPower, `R17TableBChunk02Certificate, `R17NarrowFunsB02ChunkPower, `R17ActualB02IndexPower, `R17TableBChunk03Certificate, `R17NarrowFunsB03ChunkPower, `R17ActualB03IndexPower, `R17TableBChunk04Certificate, `R17NarrowFunsB04ChunkPower, `R17ActualB04IndexPower, `R17TableBChunk05Certificate, `R17NarrowFunsB05ChunkPower, `R17ActualB05IndexPower, `R17TableBChunk06Certificate, `R17NarrowFunsB06ChunkPower, `R17ActualB06IndexPower, `R17TableBChunk07Certificate, `R17NarrowFunsB07ChunkPower, `R17ActualB07IndexPower, `R17TableBChunk08Certificate, `R17NarrowFunsB08ChunkPower, `R17ActualB08IndexPower, `R17TableBChunk09Certificate, `R17NarrowFunsB09ChunkPower, `R17ActualB09IndexPower, `R17TableBChunk10Certificate, `R17NarrowFunsB10ChunkPower, `R17ActualB10IndexPower, `R17TableBChunk11Certificate, `R17NarrowFunsB11ChunkPower, `R17ActualB11IndexPower, `R17TableBChunk12Certificate, `R17NarrowFunsB12ChunkPower, `R17ActualB12IndexPower, `R17TableBChunk13Certificate, `R17NarrowFunsB13ChunkPower, `R17ActualB13IndexPower, `R17TableBChunk14Certificate, `R17NarrowFunsB14ChunkPower, `R17ActualB14IndexPower, `R17TableBChunk15Certificate, `R17NarrowFunsB15ChunkPower, `R17ActualB15IndexPower, `R17ZPowAddition, `R17ActualWholeTablePower, `R17CircleCoordinateMulBridge, `R17CircleCoordinatePowerBridge, `R17TableCirclePowerBridge, `R17FibrePointStoredDomain, `R17FibrePointActualSuccess ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ4_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ4_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ4_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ4_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ4_AUDIT_COMPLETE declarations={count} modules={selected.size}"
