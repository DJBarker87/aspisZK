import Port18COHERENCE_Kernel
import Port18COHERENCE_CompatibilityLoad

/- The same minimal imported baseline as CheckedDomain. All replay results are
   disposable: no setEnv, unchecked insertion, or exported test declarations. -/
open Lean in
run_elab do
  let baseline ← getEnv
  let theoremInfo := fun (n : Name) (ty value : Expr) =>
    ConstantInfo.thmInfo { name := n, levelParams := [], type := ty, value := value }
  let singleton := fun (c : ConstantInfo) => ({} : Std.HashMap Name ConstantInfo).insert c.name c
  let expectRejected := fun (label : String) (cs : Std.HashMap Name ConstantInfo) => do
    let rejected ← try
      let _ ← Port18COHERENCE_Kernel.replay cs baseline
      pure false
    catch ex =>
      IO.println s!"REJECTED {label}: {ex}"
      pure true
    unless rejected do throw (IO.userError s!"EXPECTED REJECTION WAS ACCEPTED: {label}")
  let bad := theoremInfo `Port18VALIDATE_bad (mkConst ``False) (mkConst ``True.intro)
  expectRejected "closed False theorem with True.intro" (singleton bad)
  let selfName := `Port18VALIDATE_freshSelf
  unless (baseline.toKernelEnv.find? selfName).isNone do throwError "self name already populated"
  let self := theoremInfo selfName (mkConst ``False) (mkConst selfName)
  expectRejected "fresh self reference (absent from baseline)" (singleton self)
  let a := `Port18VALIDATE_cycleA
  let b := `Port18VALIDATE_cycleB
  unless (baseline.toKernelEnv.find? a).isNone && (baseline.toKernelEnv.find? b).isNone do
    throwError "cycle names already populated"
  expectRejected "fresh two-name cycle" ((singleton (theoremInfo a (mkConst ``False) (mkConst b))).insert b
    (theoremInfo b (mkConst ``False) (mkConst a)))
  let projectAxiom : ConstantInfo := .axiomInfo {
    name := `Port18VALIDATE_projectAxiom, levelParams := [], type := mkConst ``False, isUnsafe := false }
  expectRejected "project axiom" (singleton projectAxiom)
  for (label, safety) in [("unsafe input", DefinitionSafety.unsafe), ("partial input", DefinitionSafety.partial)] do
    let c : ConstantInfo := .defnInfo {
      name := Name.mkSimple ("Port18VALIDATE_" ++ label), levelParams := [],
      type := mkConst ``Nat, value := mkNatLit 0, hints := .opaque, safety := safety }
    expectRejected label (singleton c)
  -- Exercise exactly the complete sameDeclaration guard used in every stage.
  let some old := baseline.checked.get.find? ``True.intro | throwError "missing baseline constructor"
  unless Port18COHERENCE_Load.sameDeclaration old old do throwError "identity guard rejected exact input"
  let mismatch := theoremInfo ``True.intro (mkConst ``False) (mkConst ``True.intro)
  if Port18COHERENCE_Load.sameDeclaration old mismatch then
    throwError "stage guard accepted mismatched pre-existing declaration"
  IO.println "REJECTED mismatched pre-existing declaration by actual stage sameDeclaration guard"
  let good := theoremInfo `Port18VALIDATE_valid (mkConst ``True) (mkConst ``True.intro)
  unless (baseline.toKernelEnv.find? good.name).isNone do throwError "valid name already populated"
  let checked ← Port18COHERENCE_Kernel.replay (singleton good) baseline
  let some actual := checked.toKernelEnv.find? good.name | throwError "valid declaration missing"
  unless Port18COHERENCE_Load.sameDeclaration good actual do
    throwError "reconstructed type/value/metadata mismatch"
  -- A subsequent kernel check consumes the exact reconstructed theorem.
  let consumer := theoremInfo `Port18VALIDATE_consumer (mkConst ``True) (mkConst good.name)
  let consumed ← Port18COHERENCE_Kernel.replay (singleton consumer) checked
  let some actualConsumer := consumed.toKernelEnv.find? consumer.name | throwError "consumer missing"
  unless Port18COHERENCE_Load.sameDeclaration consumer actualConsumer do throwError "consumer differs"
  for n in [bad.name, selfName, a, b, projectAxiom.name] do
    unless (consumed.toKernelEnv.find? n).isNone do throwError "rejected declaration leaked: {n}"
  unless (← getEnv).toKernelEnv.find? good.name |>.isNone do throwError "disposable test escaped"
  IO.println "ACCEPTED exact valid : True := True.intro and dependent consumer; no axioms in either proof closure; disposable environments only"
