import TAS_FinalB
open Lean Elab Command Meta

def changedPrefixes : List Name := [`R0P.Public, `AspisR1.PublicOptionShape, `AspisR1.SemanticPublicWire, `AspisR1.PublicByteCodec, `AspisR1.PublicCodecAgreement, `AspisR1.SemanticPublicByteBinding, `AspisR1.SemanticPublicCodecComplete, `AspisR1.SemanticPublicWireRoundTrip]

partial def reach (env : Environment) (start : Name) : StateM (NameSet × Array Name) Unit := do
  let (seen, hits) ← get
  if seen.contains start then return
  set (seen.insert start, hits)
  if changedPrefixes.any (·.isPrefixOf start) then
    modify fun (s, h) => (s, h.push start)
    return
  match env.find? start with
  | some (.defnInfo d) =>
      for c in d.type.getUsedConstants ++ d.value.getUsedConstants do reach env c
  | some ci =>
      for c in ci.type.getUsedConstants do reach env c
  | none => pure ()

elab "#pin2top " n:ident : command => do
  let env ← getEnv
  let some ci := env.find? n.getId | throwError "missing"
  let cs := ci.type.getUsedConstants
  logInfo m!"{n.getId}: {cs.size} constants in statement: {cs.toList}"
  let ((), (_, hits)) := (do for c in cs do reach env c).run ({}, #[])
  logInfo m!"changed declarations reached by unfolding definitions in the statement: {hits.size}: {hits.toList.take 60}"

#pin2top AspisR1.TAS_FinalB.deployed_splitB
#pin2top AspisR1.TAS_FinalB.deployed_charge
set_option pp.proofs false in
#check @AspisR1.TAS_FinalB.deployed_splitB
set_option pp.proofs false in
#check @AspisR1.TAS_FinalB.deployed_charge
