from pathlib import Path
import json
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-typedfull-current-20261017');d=json.loads((W/'selected-read-reverse-frontier.json').read_text());G=d['modules'];D=json.loads((W/'external-inputs.json').read_text());current=set(D['modules'])|set(json.loads((W/'sources/SOURCE-MANIFEST.json').read_text())['modules']);seeds=set(d['conflicting_historical_objects'])|{'FS2.Duplex','AspisV8R19.UniformStateFirstHit','AspisFormal.CircleGroupOrder'}
def analyze(target,override):
 seen=set()
 def visit(n):
  if n in seen:return
  seen.add(n)
  for dep in override.get(n,G[n]['imports']):visit(dep)
 visit(target);bad=seeds&seen
 while True:
  more={n for n in seen if set(override.get(n,G[n]['imports']))&bad}-bad
  if not more:break
  bad|=more
 order=[];done=set()
 def topo(n):
  if n in done:return
  for dep in override.get(n,G[n]['imports']):topo(dep)
  done.add(n)
  if n in bad and n not in current:order.append(n)
 topo(target)
 return {'target':target,'total_imports':len(seen),'seed_reverse_closure':len(bad),'fresh_reverse_not_current':len(bad-current),'fresh_topological':order,'off_reverse_not_current':len(seen-bad-current)}
base={};public={'R1SelectedTranscriptParams':['Init','R1SelectedChallengeMap','R1SemanticPublicCodecComplete']};both=public|{'R1SelectedChallengeMap':['Init','R0C.ModuloField','R0P.SemD2']}
result={k:[analyze(t,v) for t in d['targets']] for k,v in [('existing',base),('virtual_public_split',public),('virtual_public_sigma_split',both)]};(W/'selected-read-split-analysis.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:[{a:b for a,b in q.items() if a!='fresh_topological'} for q in v] for k,v in result.items()},indent=2))
