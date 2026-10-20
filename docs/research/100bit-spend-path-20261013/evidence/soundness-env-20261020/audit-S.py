"""Audit every declaration owned by current source modules, in disjoint batches.
Uses Lean.collectAxioms, the implementation behind #print axioms; no theorem changes.
Usage: audit-S.py preflight | final
"""
import json,re,hashlib,subprocess,time,sys
from pathlib import Path
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019');D=J/'evidence-S';T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[json.loads(l) for l in (D/'status.jsonl').read_text().splitlines()]
current={r['module'] for r in records if r['status'].startswith('current')}
man=json.loads((D/'manifest-S.json').read_text())
done=set()
if (D/'axioms-batches.jsonl').exists():
 for l in (D/'axioms-batches.jsonl').read_text().splitlines():
  r=json.loads(l)
  if r['exit']==0:done.update(r['modules'])
modules=[e['module'] for e in man['order'] if e['module'] in current and e['module'] not in done]
if sys.argv[1]=='preflight':modules=modules[:30]
for offset in range(0,len(modules),30):
 batch=modules[offset:offset+30];n=len(list(D.glob('audit-source-*.lean')));name=f'SoundnessClosureAudit{n:03}'
 src='import Lean\n'+''.join('import '+m+'\n' for m in batch)
 names=', '.join('`'+m for m in batch)
 src+='''\nopen Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := ['''+names+''']
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
'''
 (D/f'audit-source-{n:03}.lean').write_text(src)
 path=J/'sources-S'/(name+'.lean');path.write_text(src)
 a=next((a for a in range(6999,6449,-1) if not (T/f'out-{a}.log').exists()),None)
 if a is None:print('audit attempt range exhausted');break
 fp=hashlib.sha256(';'.join(m+'='+sha(J/'objects-S'/(m.replace('.','/')+'.olean')) for m in sorted(batch)).encode()).hexdigest()[:16]
 cmd=['sh',str(D/'run-S.sh'),str(a),name,'S','7000','7',fp]
 start=time.time();p=subprocess.run(cmd,capture_output=True,text=True)
 out=(T/f'out-{a}.log').read_text() if (T/f'out-{a}.log').exists() else p.stdout+p.stderr
 tl=(T/f'time-{a}.log').read_text() if (T/f'time-{a}.log').exists() else ''
 (D/f'out-{a}.log').write_text(out);(D/f'time-{a}.log').write_text(tl);(D/f'launcher-{a}.log').write_text(p.stdout+p.stderr)
 ex=re.search(r'^exit=(\d+)',out,re.M);ex=int(ex.group(1)) if ex else p.returncode
 def tv(pat):
  m=re.search(pat,tl);return m.group(1).strip() if m else None
 lines=[f'{m.group(1)} | {m.group(2)} | '+re.sub(r'\s+', ' ', m.group(3)) for m in re.finditer(r'^S_AXIOMS ([^\n|]+) \| ([^\n|]+) \| (\[[^\]]*\])', out, re.M)]
 counts={m:0 for m in batch};nonstandard=[]
 for l in lines:
  owner,decl,ax=l.split(' | ');counts[owner]+=1
  axs=[s.strip() for s in ax.strip('[]').split(',') if s.strip()]
  if set(axs)-{'propext','Classical.choice','Quot.sound'}:nonstandard.append({'module':owner,'declaration':decl,'axioms':axs})
 r={'attempt':a,'module':name,'modules':batch,'source_revision':man['repo_revision'],'source_sha256':sha(path),'deps_fingerprint':fp,'command':cmd,'exit':ex,'wall':tv(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),'wall_seconds_including_lock':time.time()-start,'peak_rss_kib':int(tv(r'Maximum resident set size \(kbytes\): (\d+)') or 0),'swaps':int(tv(r'Swaps: (\d+)') or 0),'axioms_api':'Lean.collectAxioms (same as #print axioms), every owned declaration including definitions and opaque types','declaration_counts':counts,'nonstandard':nonstandard,'axiom_reports':len(lines),'errors':[l for l in out.splitlines() if 'error' in l],'out_sha256':sha(D/f'out-{a}.log')}
 with (D/'axioms-batches.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(a,name,'exit',ex,'declarations',len(lines),'nonstandard',len(nonstandard),flush=True)
 if ex!=0:print('Audit batch failed; never retried',flush=True)
