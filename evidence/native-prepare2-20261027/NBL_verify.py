from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
receipts=sorted([json.loads(p.read_text()) for p in E.glob('NBL_[LK]*/receipt.json')],key=lambda r:r['attempt'])
errors=[];qualifications=[]
lean=[r for r in receipts if r['kind']=='lean'];kani=[r for r in receipts if r['kind']=='kani']
for r in receipts:
 a=r['attempt'];ad=json.loads((E/(a+'-reservation.json')).read_text())
 if ad.get('allowed') is not True:errors.append(a+' not admitted')
 if r['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append(a+' caps mismatch')
 if str(r['swaps'])!='0':errors.append(a+' swap')
 if r['kind']=='kani':
  graph=json.loads((E/(a+'-graph-check.json')).read_text())
  lock=json.loads((E/(a+'-lock-check.json')).read_text())
  if graph.get('graph_matches_frozen') is not True or lock.get('unchanged') is not True:errors.append(a+' graph/lock')
  if r['env'].get('CARGO_NET_OFFLINE')!='true' or r['env'].get('CARGO_PROFILE_DEV_OPT_LEVEL')!='3':errors.append(a+' optimization/offline')
 if r['kind']=='lean' and r['exit_status']==0:
  for line in r['print_axioms']:
   if any(x.strip() not in ['propext','Classical.choice','Quot.sound'] for x in re.findall(r'\[([^]]*)\]',line)[0].split(',') if x.strip()):errors.append(a+' nonstandard axiom')
for p in sorted((R/'lean').glob('NBL_*.lean')):
 runs=[r for r in lean if r['module']==p.stem and r['exit_status']==0]
 if not runs:errors.append(p.name+' no accepted compile');continue
 last=runs[-1]
 source=E/last['attempt']/'sources/NBL_generated'/p.name
 if source.read_bytes()!=p.read_bytes():errors.append(p.name+' accepted source mismatch')
 code=re.sub(r'/\-.*?\-/|--[^\n]*','',p.read_text(),flags=re.S)
 if re.search(r'\b(sorry|admit|native_decide|axiom)\b',code) or re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',code):errors.append(p.name+' forbidden source')
for name in ['NBL_make_finish.py','NBL_make_effect_query.py','NBL_make_material_hash.py','NBL_make_prepare_hash.py','NBL_audit.py']:
 r=subprocess.run(['python3',str(E/name),'--check'],cwd=R,capture_output=True,text=True)
 if r.returncode:errors.append(name+' --check failed: '+r.stderr)
if len(lean)!=100:errors.append('expected exact100 actual Lean attempts')
if len(kani)>60:errors.append('Kani budget exceeded')
assoc=json.loads((E/'NBL_ASSOCIATIONS.json').read_text())
if not assoc['all_cut_token_checks'] or assoc['frozen_source_differences']:errors.append('source/cut inventory')
qualifications+=['L016/K003 overlapped for5.469 seconds before the own atomic guard: NBL_SCOPE_OVERLAP.md.',
 'Failed receipts/diagnostic sorryAx roots are retained and excluded; current modules have accepted exact source snapshots.',
 'Historical LPb frozen replay/no-drift-reachability not completed: ZERO native credit to those historical stages.',
 'K016-K019 View stub/caller failures remain excluded; K020 proves only returned-Result continuation.',
 'Complete native preparation bridge remains OPEN; no release/full frozen manifest replay was claimed.']
ledger=dict(actual_lean=len(lean),actual_kani=len(kani),preflight_only=['NBL_L023','NBL_K001'],
 passed_lean=sum(r['exit_status']==0 for r in lean),passed_kani=sum(r['exit_status']==0 for r in kani),
 attempts=[{k:r[k] for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']} for r in receipts])
(E/'NBL_LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n')
report=dict(errors=errors,qualifications=qualifications,accepted_modules=len(list((R/'lean').glob('NBL_*.lean'))),
 final_audit=next((r['attempt'] for r in reversed(lean) if r['module']=='NBL_Audit' and r['exit_status']==0),None))
(E/'NBL_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
if errors:raise SystemExit(1)
