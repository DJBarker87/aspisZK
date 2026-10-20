#!/usr/bin/env python3
"""Validate retained evidence without replaying any compiler or solver."""
import hashlib,json,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
manifest=json.loads((E/'new-cone-manifest.json').read_text())
source=json.loads((E/'source-release.json').read_text())
mods=['R1Z/'+m for m in manifest['modules']]
remote='/home/dombarker/project-offloads/aspis-joint-20261019'
cmd='set -e\n'+'\n'.join('sha256sum '+remote+'/'+kind+'/'+m+suffix for m in mods for kind,suffix in [('sources','.lean'),('objects','.olean')])
objects={}
for line in subprocess.check_output(['ssh','dombarker@100.108.41.90',cmd],text=True).splitlines():
 h,p=line.split();objects[p]=h
(E/'final-host-hashes.json').write_text(json.dumps(objects,indent=2)+'\n')
allowed={'propext','Classical.choice','Quot.sound'}
accepted=[]
for row in source:
 p=Path(row['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
 mod='R1Z/'+p.stem
 assert objects[remote+'/sources/'+mod+'.lean']==row['sha256']
 a=row['accepted_attempt'];rec=json.loads((E/'lean'/f'lean-{a}.json').read_text())
 log=(E/'lean'/f'out-{a}.log').read_text()
 assert re.search(r'^exit=0$',log,re.M)
 assert 'sorryAx' not in log
 assert rec['cgroup_memory_max_gib']==8
 for name,h in rec['deps']:
  key=remote+'/objects/'+name.replace('.','/')+'.olean'
  if key in objects:assert objects[key]==h,(a,name)
 # All final theorem declarations must be explicitly audited in the source.
 ns=None
 for line in p.read_text().splitlines():
  if line.startswith('namespace '):ns=line.split()[1]
  mt=re.match(r'theorem (\w+)',line)
  if mt:assert ns+'.'+mt[1] in manifest['audit_names'],(p,mt[1])
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option (maxRecDepth|maxHeartbeats)',p.read_text(),re.M)
 accepted.append(a)
audit=(E/'lean/out-8239.log').read_text()
lines=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",audit,re.S)
assert {x[0] for x in lines}==set(manifest['audit_names'])
for name,ax in lines:assert set(re.findall(r'[\w.]+',ax))<=allowed,(name,ax)
r=json.loads((E/'lean/lean-8239.json').read_text());tm=(E/'lean/time-8239.log').read_text()
result=dict(module='R1Z.ProverCommit6Audit',attempt=8239,source_revision=source[0]['source_revision'],
 source_sha256=r['source_sha256'],deps_fingerprint=r['deps_fingerprint'],exit_status=0,
 wall_time=re.search(r'Elapsed.*: (.+)',tm)[1],peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',tm)[1]),
 swaps=int(re.search(r'Swaps: (\d+)',tm)[1]),axioms=[dict(declaration=n,axioms=re.findall(r'[\w.]+',ax)) for n,ax in lines],
 audit_declarations=len(lines),release_modules=len(source),accepted_attempts=accepted,
 host_source_and_own_dependency_objects_current=True,full_existing_manifest_replayed=False,
 reason='Only additive modules changed; each focused target checked and the complete new cone imported once in final audit.',
 complete_source_checklist_rows_closed=0,next_attempt=8240)
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['exit_status','audit_declarations','release_modules','wall_time','peak_rss_kib','swaps','next_attempt']}))
