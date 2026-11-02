import Lean
open Lean
/-- Deliberately malformed test object, never an accepted proof or release input. -/
unsafe def main (_ : List String) : IO UInt32 := do
 let c := ConstantInfo.defnInfo {
  name := `NER_Plant.parent
  levelParams := []
  type := mkConst ``Nat
  value := mkConst `NER_Plant.missing
  hints := .opaque
  safety := .safe
 }
 saveModuleData "NER_PlantObject.olean" `NER_PlantObject {
  isModule := false
  imports := #[]
  constants := #[c]
  constNames := #[c.name]
  extraConstNames := #[]
  entries := #[]
 }
 let control := ConstantInfo.defnInfo {
  name := `NER_PlantControl.parent
  levelParams := []
  type := mkConst ``Nat
  value := mkNatLit 0
  hints := .opaque
  safety := .safe
 }
 saveModuleData "NER_PlantControl.olean" `NER_PlantControl {
  isModule := false
  imports := #[]
  constants := #[control]
  constNames := #[control.name]
  extraConstNames := #[]
  entries := #[]
 }
 return 0
