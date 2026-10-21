#!/usr/bin/env python3
"""Validate the additive packet and emit a reproducible source/axiom audit."""
import hashlib,json,pathlib,re,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2]
B=ROOT/'docs/research/100bit-spend-path-20261013'; OUT=B/'evidence/r22-total-20261021'
base='6546eb41f37d2d49f69b0386922b1b46269b039a'
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((OUT/'manifest.json').read_text());latest={};failures=[]
for r in manifest['attempts']:
 d=OUT/f"{r['module']}-{r['attempt']}";src=d/'source.lean.txt'
 assert sha(src)==r['source_sha256'],src
 assert all(k in r for k in ('module','attempt','source_revision','source_sha256','deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps','axiom_lines'))
 assert r['swaps']==0
 if r['exit']:failures.append({'module':r['module'],'attempt':r['attempt'],'exit':r['exit'],'errors':r['errors']})
 latest[r['module']]=r
audit_names=('R22TotalPacketAudit','R22TotalRowPacketAudit','R22TotalConstantPacketAudit')
assert all(latest[n]['exit']==0 for n in audit_names),'Final compatible audits not green'
for name,r in latest.items():
 assert r['exit']==0,name
 assert sha(B/'lean'/f'{name}.lean')==r['source_sha256'],name
 for a in r['axiom_lines']:
  if 'depends on axioms' in a:
   toks=set(re.findall(r'\w+(?:\.\w+)*',a.split('[',1)[1].split(']',1)[0]))
   assert toks<={'propext','Classical.choice','Quot.sound'},(name,a)
full='\n'.join(a for n in audit_names for a in latest[n]['axiom_lines']);theorems=[]
for p in sorted((B/'lean').glob('R22Total*.lean')):
 txt=p.read_text()
 assert not re.search(r'(?m)^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option\s+(?:maxHeartbeats|maxRecDepth)',txt),p
 ns=re.search(r'(?m)^namespace (AspisR1\S*)',txt)
 for m in re.finditer(r'(?m)^theorem (\S+)',txt):
  name=ns[1]+'.'+m[1]
  assert "'"+name+"'" in full,('Missing final audit',name)
  theorems.append(name)
changed=git('diff','--name-status',base,'--','docs/research/100bit-spend-path-20261013/lean').splitlines()
assert all(l.startswith('A\t') and l.split('\t',1)[1].split('/')[-1].startswith('R22Total') for l in changed)
assert not git('diff','--name-only',base,'--','crates','programs')
# Preserve the supplied headline and the boundary definition verbatim.
endpoints=['R1FinalSoundnessBinPerQueryR19.lean','R1FinalSoundness.lean','R1FinalSoundnessHeadline.lean']
pins=[]
for name in endpoints:
 p=B/'lean'/name;old=subprocess.check_output(['git','show',base+':'+str(p.relative_to(ROOT))],cwd=ROOT)
 assert p.read_bytes()==old
 pins.append({'path':str(p.relative_to(ROOT)),'sha256':sha(p),'size':p.stat().st_size,'unchanged_from_base':True})
diff=git('diff',base,'--',*[str((B/'lean'/n).relative_to(ROOT)) for n in endpoints])
assert not diff
(OUT/'endpoint-signature.diff').write_text(diff)
res={'base':base,'source_revision':git('rev-parse','HEAD').strip(),'schema':'r22-total-final-audit-v1',
'new_theorems':len(theorems),'theorems':theorems,'latest_successful_modules':len(latest),
'compile_attempts':len(manifest['attempts']),'retained_failures':failures,
'peak_rss_bytes':max(r['peak_rss_bytes'] for r in manifest['attempts']),
'swaps':0,'standard_axioms_only':True,'endpoint_pins':pins,
'boundary_field_unchanged':'h_R22 : s.R22',
'shipped_source_changes':[],'existing_lean_changes':[],
'R22_status':'Local total cones proved; whole frozen verifier R22 remains open for documented caller/source/P6 joins.',
'joint_environment_status':'Blocked by retained global instance collisions; three compatible audit groups only.',
'final_packet_audits':{n:{k:latest[n][k] for k in ('exit','wall_seconds','peak_rss_bytes','swaps','source_sha256','deps_fingerprint')} for n in audit_names}}
(OUT/'final-audit.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:res[k] for k in ('new_theorems','latest_successful_modules','compile_attempts','peak_rss_bytes','swaps','standard_axioms_only','final_packet_audits')},indent=2))
