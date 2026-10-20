import json,re,hashlib,subprocess,time
from pathlib import Path
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019');D=J/'evidence-S';T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');O=J/'objects-S'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
man=json.loads((D/'manifest-S.json').read_text());mods={e['module']:e for e in man['order']}
def closure(m,seen=None):
 seen=set() if seen is None else seen
 if m in seen:return seen
 seen.add(m)
 if m in mods:
  for dep in mods[m]['imports']:closure(dep,seen)
 return seen
bad=next(r for r in map(json.loads,(D/'continuation-axioms-batches.jsonl').read_text().splitlines()) if r['attempt']==7909)
assert bad['exit']!=0
pair={'AspisR1PublicSerializer.Types','AspisR1RecordParser.Types'}
groups={'serializer':[],'record-parser':[],'neutral':[]}
for m in bad['requested_modules']:
 c=closure(m);assert not pair<=c
 key='serializer' if 'AspisR1PublicSerializer.Types' in c else 'record-parser' if 'AspisR1RecordParser.Types' in c else 'neutral';groups[key].append(m)
batches=[(k,ms,False) for k,ms in groups.items() if ms]
rep=json.loads((D/'collision-closures.json').read_text());rep['additional_audit_collision']={'declaration':'instDiscriminantErrorIsize','owners':sorted(pair),'failed_audit_attempt':7909,'roots_requiring_both':[m for m in man['roots'] if pair<=closure(m)],'repair_partitions':groups};(D/'collision-closures.json').write_text(json.dumps(rep,indent=2)+'\n')
for i,(partition,batch,external) in enumerate(batches):
 name=f'SoundnessClosureAuditCollisionRepair{i:03}';a=7960+i;assert a<=7999 and not (T/f'out-{a}.log').exists()
 src='import Lean\n'+''.join('import '+m+'\n' for m in batch)
 src+='''\nopen Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := ['''+', '.join('`'+m for m in batch)+''']
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if '''+('(`CompPoly).isPrefixOf owner' if external else 'owners.contains owner')+''' then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
'''
 p=J/'sources-S'/(name+'.lean');p.write_text(src);(D/(name+'.lean')).write_text(src)
 def object_for(m):
  if external:return Path(json.loads((D/'continuation-libraries.json').read_text())[m]['path'])
  return O/(m.replace('.','/')+'.olean')
 fp=hashlib.sha256(';'.join(m+'='+sha(object_for(m)) for m in sorted(batch)).encode()).hexdigest()[:16]
 cmd=['sh',str(D/'run-S.sh'),str(a),name,'S','7000','7',fp];before=time.time();proc=subprocess.run(cmd,capture_output=True,text=True)
 out=(T/f'out-{a}.log').read_text() if (T/f'out-{a}.log').exists() else proc.stdout+proc.stderr;tl=(T/f'time-{a}.log').read_text() if (T/f'time-{a}.log').exists() else ''
 (D/f'out-{a}.log').write_text(out);(D/f'time-{a}.log').write_text(tl);(D/f'launcher-{a}.log').write_text(proc.stdout+proc.stderr)
 ex=re.search(r'^exit=(\d+)',out,re.M);ex=int(ex.group(1)) if ex else proc.returncode
 counts={m:0 for m in batch};ns=[];reports=list(re.finditer(r'^S_AXIOMS ([^\n|]+) \| ([^\n|]+) \| (\[[^\]]*\])',out,re.M))
 for match in reports:
  owner,decl,ax=match.groups();counts[owner]=counts.get(owner,0)+1;axs=[re.sub(r'\s+',' ',x).strip() for x in ax.strip('[]').split(',') if x.strip()]
  if set(axs)-{'propext','Classical.choice','Quot.sound'}:ns.append({'module':owner,'declaration':decl,'axioms':axs})
 def tv(pat):
  mm=re.search(pat,tl);return mm.group(1).strip() if mm else None
 r={'attempt':a,'module':name,'modules':list(counts),'requested_modules':batch,'partition':partition,'source_revision':man['repo_revision'],'source_sha256':sha(p),'deps_fingerprint':fp,'command':cmd,'exit':ex,'wall':tv(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),'wall_seconds_including_lock':time.time()-before,'peak_rss_kib':int(tv(r'Maximum resident set size \(kbytes\): (\d+)') or 0),'swaps':int(tv(r'Swaps: (\d+)') or 0),'axioms_api':'Lean.collectAxioms (same as #print axioms), every owned declaration','declaration_counts':counts,'nonstandard':ns,'axiom_reports':len(reports),'errors':[l for l in out.splitlines() if 'error' in l],'out_sha256':sha(D/f'out-{a}.log')}
 with (D/'continuation-axioms-batches.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(a,partition,'exit',ex,'declarations',len(reports),'nonstandard',len(ns),flush=True)
