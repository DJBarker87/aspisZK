"""Use the last assigned attempt to inspect the joint-import-blocked batch.
Distinct import environments preserve, rather than conceal, the joint-import failure.
No source proof is rerun and no namespace is rewritten.
"""
import json,hashlib,re,subprocess,time
from pathlib import Path
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019');D=J/'evidence-S';T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rs=list(map(json.loads,(D/'axioms-batches.jsonl').read_text().splitlines()));bad=next(r for r in rs if r['attempt']==6975);batch=bad['modules'];name='SoundnessIsolatedAxiomAudit';a=6970
assert not (T/f'out-{a}.log').exists()
src='import Lean\nopen Lean\n#eval show IO Unit from do\n  let owners : List Name := ['+', '.join('`'+m for m in batch)+''']
  for owner in owners do
    let env ← importModules #[{ module := owner }] {} (loadExts := true)
    let action : CoreM Unit := do
      let current ← getEnv
      for entry in current.constants.toList do
        let decl := entry.1
        if let some idx := current.getModuleIdxFor? decl then
          let moduleOwner := current.header.moduleNames[idx]!
          if moduleOwner == owner then
            let axs ← collectAxioms decl
            liftIO <| IO.println s!"S_AXIOMS {moduleOwner} | {decl} | {axs.toList}"
    CoreM.toIO' action { fileName := "isolated-axiom-audit", fileMap := FileMap.ofString "" } { env := env }
'''
p=J/'sources-S'/(name+'.lean');p.write_text(src);(D/'audit-isolated-source.lean').write_text(src)
fp=hashlib.sha256(';'.join(m+'='+sha(J/'objects-S'/(m.replace('.','/')+'.olean')) for m in sorted(batch)).encode()).hexdigest()[:16]
cmd=['sh',str(D/'run-S.sh'),str(a),name,'S','7000','7',fp]
# The launcher permits audit helper names only; use an audit-prefixed helper name.
name='SoundnessClosureAuditIsolated';q=J/'sources-S'/(name+'.lean');q.write_text(src);cmd[3]=name
start=time.time();proc=subprocess.run(cmd,capture_output=True,text=True)
out=(T/f'out-{a}.log').read_text() if (T/f'out-{a}.log').exists() else proc.stdout+proc.stderr;tl=(T/f'time-{a}.log').read_text() if (T/f'time-{a}.log').exists() else ''
(D/f'out-{a}.log').write_text(out);(D/f'time-{a}.log').write_text(tl);(D/f'launcher-{a}.log').write_text(proc.stdout+proc.stderr)
ex=re.search(r'^exit=(\d+)',out,re.M);ex=int(ex.group(1)) if ex else proc.returncode
counts={m:0 for m in batch};ns=[];reports=list(re.finditer(r'^S_AXIOMS ([^\n|]+) \| ([^\n|]+) \| (\[[^\]]*\])',out,re.M))
for match in reports:
 owner,decl,ax=match.groups();counts[owner]+=1;axs=[x.strip() for x in ax.strip('[]').split(',') if x.strip()]
 if set(axs)-{'propext','Classical.choice','Quot.sound'}:ns.append({'module':owner,'declaration':decl,'axioms':axs})
def tv(pat):
 m=re.search(pat,tl);return m.group(1).strip() if m else None
r={'attempt':a,'module':name,'modules':batch,'source_revision':json.loads((D/'manifest-S.json').read_text())['repo_revision'],'source_sha256':sha(q),'deps_fingerprint':fp,'command':cmd,'exit':ex,'wall':tv(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),'wall_seconds_including_lock':time.time()-start,'peak_rss_kib':int(tv(r'Maximum resident set size \(kbytes\): (\d+)') or 0),'swaps':int(tv(r'Swaps: (\d+)') or 0),'axioms_api':'Lean.collectAxioms; separate importModules environments per source module; does not establish joint import compatibility','declaration_counts':counts,'nonstandard':ns,'axiom_reports':len(reports),'errors':[l for l in out.splitlines() if 'error' in l],'out_sha256':sha(D/f'out-{a}.log'),'joint_import_blocker_attempt':6975}
with (D/'axioms-batches.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
print(a,name,'exit',ex,'declarations',len(reports),'nonstandard',len(ns),flush=True)
