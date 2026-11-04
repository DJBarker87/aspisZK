import Lean
import NGI_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 logInfo m!"NGI_CERT_MODULES {(toJson (env.header.moduleNames.map (fun n => n.toString))).compress}"
 for n in (#[`NGF_NEX_ReadDomains.after_window,`NGF_NEX_ReadDomains.disjoint,`NGF_NEX_ReadDomains.snapshot_window,`NGF_NEX_SnapshotBoxOracle.result_state_effects,`NGF_NEX_SnapshotParent.result_state_effects,`NGF_NEX_StatementExt.complete,`NGF_NEX_TerminalDomain.fixed_carrier,`NGF_NEX_TerminalDomain.wrong_length,`NGF_NEY_Field00.alignment,`NGF_NEY_Field01.alignment,`NGF_NEY_Field02.alignment,`NGF_NEY_Field03.alignment,`NGF_NEY_Field04.alignment,`NGF_NEY_Field05.alignment,`NGF_NEY_Field06.alignment,`NGF_NEY_Field07.alignment,`NGF_NEY_Field08.alignment,`NGF_NEY_Field09.alignment,`NGF_NEY_Field10.alignment,`NGF_NEY_Field11.alignment,`NGF_NEY_Field12.alignment,`NGF_NEY_Field13.alignment,`NGF_NEY_Field14.alignment,`NGF_NEY_Field15.alignment,`NGF_NEY_Field16.alignment,`NGF_NEY_Field17.alignment,`NGF_NEY_Field18.alignment,`NGF_NEY_Field19.alignment,`NGF_NEY_Field20.alignment,`NGF_NEY_Field21.alignment,`NGF_NEY_Field22.alignment,`NGF_NEY_Field23.alignment,`NGF_NEY_Field24.alignment,`NGF_NEY_Field25.alignment,`NGF_NEY_ReachedResultDomains.binding_argument,`NGF_NEY_ReachedResultDomains.ready_payload,`NGF_NEY_ResultConstants.layout,`NGF_NEY_ResultConstants.partition,`NGF_NEY_ResultProjection.stores_spec,`NGF_NEY_ResultStores.stores_observe,`NGF_NEY_TerminalGeometry.header_constants,`NGF_NEY_TerminalGeometry.kind_same,`NGF_NEY_TerminalGeometry.payment_offset,`NGF_NEY_TerminalGeometry.payment_window] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson ((env.getModuleIdxFor? n).map ModuleIdx.toNat)),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGI_CERT_ENTRY {entry.compress}"
