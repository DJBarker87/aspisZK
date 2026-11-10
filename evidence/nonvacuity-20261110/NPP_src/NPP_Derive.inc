
/-! Structural `DecidableEq` for the structure carriers of the remaining site (WideExact and the
field structures under it), by the standard deriving handler. These are new computable instances;
they add no axiom and change no existing declaration. -/
open Lean Elab Command Meta in
partial def NPP.deriveDecEq (S : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := getStructureInfo? env S | throwError "{S} is not a structure"
  let has ← liftTermElabM do
    let some ci := env.find? S | return true
    forallTelescope ci.type fun xs _ => do
      let ty := mkAppN (mkConst S (ci.levelParams.map Level.param)) xs
      return (← synthInstance? (← mkAppM ``DecidableEq #[ty])).isSome
  if has then return
  for f in info.fieldNames do
    let some pf := env.find? (S ++ f) | continue
    let heads ← liftTermElabM <| forallTelescope pf.type fun _ body => do
      let b ← whnf body
      return b.getAppFn.constName?
    if let some T := heads then
      if (getStructureInfo? env T).isSome && T != S then NPP.deriveDecEq T
  NPP.log <| Json.mkObj [("derive_DecidableEq", toJson S.toString)]
  elabCommand (← `(deriving instance DecidableEq for $(mkIdent S)))

run_cmd NPP.deriveDecEq `AspisR1Stage2.aspis_core.field.wide_exact.WideExact
