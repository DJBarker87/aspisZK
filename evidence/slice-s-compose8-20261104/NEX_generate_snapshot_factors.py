"""Add callback checks to existing factored continuations, never unfold21 reads."""
from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;path='evidence/port17release-20261024/dependency-source/S6NativeSnapshotDecoderFactoredV1.lean'
s=subprocess.check_output(['git','show','HEAD:'+path],text=True);records=[]
parts=['part_16','part_12','part_8','part_4','part_0','decode']
for idx,name in enumerate(parts):
 mod='NEX_Snapshot'+('Parent' if name=='decode' else 'Part'+name[5:]);child=None if idx==0 else 'NEX_SnapshotPart'+parts[idx-1][5:]
 a=re.search(r'^def '+name+r'\b',s,re.M).start();match=re.search(r'^\b(?:def|theorem)\b',s[a+1:],re.M);z=a+1+match.start() if match else len(s);original=s[a:z].strip()
 header=original.split(' := do',1)[0];binders=re.findall(r'\(([\w\s]+) :',header);args=' '.join(' '.join(b.split()) for b in binders);decl=header.split(' (',1)[1].split(' : Result',1)[0];decl='('+decl
 # Reuse exact parameter groups; only the continuation's child heads change.
 native=original.replace('def '+name+' (','def run (read : Read) (validate : Validate) (',1)
 native=native.replace('AspisS6NativeSnapshotReadDigest.read_digest','read').replace('pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1','validate')
 if child:native=re.sub(r'\b'+parts[idx-1]+r' bytes',child+'.run read validate bytes',native)
 imports='import S6NativeSnapshotDecoderFactoredV1\n'+('import '+child+'\n' if child else '')
 out=imports+'set_option autoImplicit false\nnoncomputable section\nnamespace '+mod+'\nopen Aeneas Aeneas.Std Result ControlFlow Error AspisR1TerminalDecoder\nopen pool_v1.pair_tree_profile AspisS6NativeSnapshotDecoderFactored\nabbrev Read := Slice U8 → Result (core.result.Result (Array aspis_core.field.M31 8#usize) atomic_statement.AtomicStatementError)\nabbrev Validate := PoolV1PairLiveSnapshotV1 → Result (core.result.Result Unit PoolV1PairLiveSnapshotErrorV1)\n'+native+'\n'
 actual='AspisS6NativeSnapshotReadDigest.read_digest pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1'
 out+=f'''theorem source {decl} :
    run {actual} {args} = AspisS6NativeSnapshotDecoderFactored.{name} {args} := by
  unfold run AspisS6NativeSnapshotDecoderFactored.{name}
'''
 if child:out+='  simp only ['+child+'.source]\n'
 out+='''  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "NEX_Snapshot" || s.startsWith "AspisS6NativeSnapshotDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl
#print axioms source
'''
 if name=='decode':out+=f'''
/-- Substitute both certified child models into the explicit full-Result G.
The existing factored/source equality supplies the original cohort endpoint. -/
theorem result_state_effects {{State : Type}} (bytes : Slice U8) (state : State) :
    (run {actual} bytes,state,([] : List Unit)) =
    (decode_pool_v1_pair_live_snapshot_v1 bytes,state,[]) := by
  exact congrArg (fun r => (r,state,([] : List Unit)))
    ((source bytes).trans (AspisS6NativeSnapshotDecoderFactored.decode_source bytes))
#print axioms result_state_effects
'''
 out+='end '+mod+'\n';(E/(mod+'.lean')).write_text(out)
 records.append(dict(module=mod,source=path,old_function=name,old_body_sha256=hashlib.sha256(original.encode()).hexdigest(),transform='only add full-Result read/validate callbacks and replace factored child with the preceding checked callback factor; no branch/order changes'))
(E/'NEX_SNAPSHOT_FACTOR_GENERATION.json').write_text(json.dumps(records,indent=1))
