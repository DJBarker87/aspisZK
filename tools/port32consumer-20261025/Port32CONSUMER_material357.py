"""Material357: eliminate same-module init; one lexical owner through all commands/audits."""
import pathlib,json
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/port32consumer-20261025'
s=(E/'Port32CONSUMER_source-356.lean.txt').read_text()
start=s.index('-- Regions remain in this process-global reference')
end=s.index('def jsonFile',start)
s=s[:start]+'''-- All loaded ModuleData/regions travel in the same command's lexical owner.
-- No explicit free and no finalizer: mapped buffers remain until process EXIT.
'''+s[end:]
s=s.replace('def load (env : Environment) : IO (Std.HashMap Name ConstantInfo) := do','def load (env : Environment) : IO (Std.HashMap Name ConstantInfo × Std.HashMap Name ConstantInfo × Array (ModuleData × CompactedRegion)) := do')
s=s.replace('  let mut selected : Std.HashMap Name ConstantInfo := {}','  let mut selected : Std.HashMap Name ConstantInfo := {}\n  let mut regions : Array (ModuleData × CompactedRegion) := #[]',1)
s=s.replace('    retained.modify (·.push part)','    regions := regions.push part')
s=s.replace('  selectedRef.set selected\n  coreNames.set reused\n','').replace('  return fresh','  return (fresh,selected,regions)')
# Retain complete original source text for independent review. The only syntactic
# update expansion is the exact constructor with all seven other fields retained.
a=s.index('set_option autoImplicit false\nnoncomputable section\nopen Aeneas')
b=s.index('\nset_option pp.all true in\n#print Port32CONSUMER.accepted_original_sdk_s2_s1',a)
composed=s[a:b]
composed=composed.replace('{rawCut with semantic := selectedPublic}', '(FirstCut.mk rawCut.proofAccount rawCut.publicAccount rawCut.raw rawCut.pub rawCut.statement selectedPublic rawCut.proof rawCut.split)')
composed=composed.replace('decode (toClaimE prepared.gamma)^i.val', '(@HPow.hPow AspisWideTower.WideExact Nat AspisWideTower.WideExact Port32CONSUMER.widePow (decode (toClaimE prepared.gamma)) i.val)')
(E/'Port32CONSUMER_ComposedSource.lean.txt').write_text(composed)
theorem_start=composed.index('theorem accepted_original_sdk_s2_s1')
theorem_end=composed.index('\n#print axioms accepted_original_sdk_s2_s1')
commands=[*composed[:theorem_start].strip().splitlines(),composed[theorem_start:theorem_end],*composed[theorem_end:].strip().splitlines(), 'set_option pp.all true in\n#print Port32CONSUMER.accepted_original_sdk_s2_s1']
commands+=['#print Port32CONSUMER.widePow', '#print axioms Port32CONSUMER.widePow']
commands+=['#print axioms '+n for n in ['AspisR1.OraclePortCompactDraft.parse_header','AspisR1.S2W_D189Consolidation.accepted_run','AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace','AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts']]
# Consumer source contains a declaration comment; parser accepts that comment together
# with theorem as before. Header commands are all one physical line in the snapshot.
commands=[x for x in commands if x]
# Prefix ends after the replay helper. Replace all external consumers/audits by the
# same single CommandElabM lexical owner, so no same-module initialized IO.Ref exists.
prefix=s[:s.index('\nopen Lean in\nrun_elab do\n  let env ← getEnv')].replace('private def strictExpr', 'def strictExpr')
recover='''
namespace Port32CONSUMER_Recover
open Lean
/-- Reconstruct only the closed, exact instance already present in the pinned
S1 theorem TYPE. Ordinary kernel checking validates its complete value/type. -/
def widePow (env : Environment) : IO Environment := do
  let some c := env.toKernelEnv.find? `AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace
    | throw (IO.userError "missing actual S1 source theorem")
  let mut todo := #[c.type]
  let mut instances : Array Expr := #[]
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if e.getAppFn.isConstOf `HPow.hPow && e.getAppArgs.size == 6 then
      let inst := e.getAppArgs[3]!
      unless !inst.hasLooseBVars && !inst.hasFVar && !inst.hasMVar do
        throw (IO.userError "power instance is not closed")
      if !(instances.any (fun a => Port32CONSUMER_Literal.strictExpr a inst)) then
        instances := instances.push inst
    match e with
    | .app f a => todo := (todo.push f).push a
    | .lam _ t v _ | .forallE _ t v _ => todo := (todo.push t).push v
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .mdata _ v | .proj _ _ v => todo := todo.push v
    | _ => pure ()
  unless instances.size == 1 do throw (IO.userError s!"power instance ambiguity {instances.size}")
  let n := `Port32CONSUMER.widePow
  let wide := mkConst `AspisWideTower.WideExact
  let ty := mkApp3 (mkConst `HPow [Level.zero,Level.zero,Level.zero]) wide (mkConst `Nat) wide
  let d := Declaration.defnDecl { name := n, levelParams := [], type := ty,
    value := instances[0]!, hints := .abbrev, safety := .safe, all := [n] }
  match env.addDeclCore (Core.getMaxHeartbeats {}).toUSize d (cancelTk? := none) with
  | .ok checked => pure checked
  | .error ex => throw (IO.userError (← ex.toMessageData {} |>.toString))
end Port32CONSUMER_Recover
'''
macro='''
macro:max x:term:max noWs "#usize" : term =>
  `(Aeneas.Std.Usize.ofNat $x (by decide))
'''
texts='\ndef Port32CONSUMER_commandTexts : Array String := #[\n'+',\n'.join('  '+json.dumps(x,ensure_ascii=False) for x in commands)+'\n]\n'
body='''
open Lean in
run_cmd do
  let env ← getEnv
  logInfo m!"PORT32_IMPORTS {env.header.modules.map (·.module)}"
  let (fresh,selected,regions) ← Port32CONSUMER_Select.load env
  let checked ← Port32CONSUMER_Kernel.replay fresh env
  let checked ← Port32CONSUMER_Recover.widePow checked
  setEnv checked
  for (n,c) in selected.toList do
    let some d := checked.toKernelEnv.find? n | throwError "missing checked {n}"
    unless Port32CONSUMER_Literal.strictDeclaration c d do
      throwError "strict checked-CI/source readback failed {n}"
  logInfo m!"PORT32_FULL_STRICT_READBACK {selected.size}"
  -- Only namespace elaboration metadata is reconstructed; no logical declaration
  -- enters here. All constants already passed the ordinary kernel above.
  for (n,_) in selected.toList do
    let mut p := n.getPrefix
    while !p.isAnonymous do
      let ns := p
      modifyEnv (·.registerNamespace ns)
      p := p.getPrefix
  for text in Port32CONSUMER_commandTexts do
    let stx ← match Parser.runParserCategory (← getEnv) `command text "Port32CONSUMER_ComposedSource" with
      | .ok stx => pure stx
      | .error e => throwError "actual consumer source parse: {e}"
    Elab.Command.elabCommand stx
    if (← get).messages.hasErrors then throwError "actual consumer elaboration failed; no closure claim"
  for n in #[`Port32CONSUMER.eq_true_of_not_eq_false, `Bool.eq_true_of_not_eq_false,
      `AspisR1.OraclePortCompactDraft.parse_header,
      `AspisR1.S2W_D189Consolidation.accepted_run,
      `AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace,
      `AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts,
      `Port32CONSUMER.accepted_original_sdk_s2_s1] do
    let some c := (← getEnv).toKernelEnv.find? n | throwError "missing audit target {n}"
    unless c.isTheorem do throwError "audit target not theorem {n}"
    let axs ← collectAxioms n
    unless axs.all Port32CONSUMER_Select.standard do throwError "rejected axioms {n}: {axs}"
    logInfo m!"PORT32_AXIOMS {n}: {axs}"
  let powAxioms ← collectAxioms `Port32CONSUMER.widePow
  unless powAxioms.all Port32CONSUMER_Select.standard do throwError "power instance axioms rejected"
  logInfo m!"PORT32_AXIOMS Port32CONSUMER.widePow: {powAxioms}"
  for (n,c) in selected.toList do
    let some d := (← getEnv).toKernelEnv.find? n | throwError "missing final CI {n}"
    unless Port32CONSUMER_Literal.strictDeclaration c d do throwError "final CI drift {n}"
  -- The owner is used only AFTER every theorem/axioms/strict-CI audit. CompactedRegion
  -- has no destructor/finalizer; no buffer is freed when this command returns.
  -- These mappings and all borrowed references remain resident until OS process exit.
  unless regions.size > 0 do throwError "no retained regions"
  logInfo m!"PORT32_COMPLETE selected={selected.size} retained_regions={regions.size}"
'''
(T/'Port32CONSUMER_Consumer.lean').write_text(prefix+recover+macro+texts+body)
print('Material357 source: single lexical owner,',len(commands),'ordinary source commands; no initialize')
