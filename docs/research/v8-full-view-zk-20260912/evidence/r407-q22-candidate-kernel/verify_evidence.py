#!/usr/bin/env python3
"""Read-only verification of saved R407 source/build evidence."""
from pathlib import Path
import hashlib, json, re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
TARGET=ROOT/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R407Q22CandidateKernel.lean'
EXPECTED='2fb00855b8588f9c40cc4de645abcdc2978a840cb38a76802330ca1b93050e89'
FOUNDATIONS={'propext','Classical.choice','Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def req(ok,msg):
    if not ok: raise AssertionError(msg)
req(sha(TARGET)==EXPECTED,'promoted source SHA mismatch')
req(sha(HERE/'R407Q22CandidateKernel.lean')==EXPECTED,'evidence source SHA mismatch')
req((TARGET.read_bytes()==(HERE/'R407Q22CandidateKernel.lean').read_bytes()),'promoted/evidence bytes differ')
rid='1790961659172355000'; stem='aspis-focus-'+rid
r=json.loads((HERE/'runs'/(stem+'.receipt.json')).read_text()); log=(HERE/'runs'/(stem+'.log')).read_text()
req(r['source_sha256']==EXPECTED and sha(HERE/'runs'/(stem+'.source.lean'))==EXPECTED,'captured source mismatch')
req(r['source_revision']=='d473563212029be91ea1032bfd2ef70ee6d68b73','source revision mismatch')
req(r['exit_status']==0 and 'Exit status: 0' in log,'compile was not green')
req(r['wall_time']=='0:01.40' and r['peak_rss_kib']==3234472 and r['swaps']==0,'metrics mismatch')
req('Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.40' in log and 'Maximum resident set size (kbytes): 3234472' in log and 'Swaps: 0' in log,'raw metrics mismatch')
req(re.findall(r"'[^\n]+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)==r['complete_print_axioms'],'all raw axiom reports mismatch')
req(r['resources']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'},'resource cap mismatch')
req(r['runner_sha256']=='d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea' and sha(HERE/'runner/run_focus.py')==r['runner_sha256'],'runner mismatch')
expected_names=['loop_candidate_kernel','challenge_candidate_kernel']
expected_reports=[f"'AspisV8R19.R407Q22CandidateKernel.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in expected_names]
norm=lambda x:' '.join(x.split())
req([norm(x) for x in r['complete_print_axioms']]==[norm(x) for x in expected_reports],'full axiom receipt mismatch')
for report in expected_reports: req(norm(report) in norm(log),'axiom report missing in log')
req('sorryAx' not in log,'sorryAx appears in successful log')
require_imports={'AspisV8R19.R402Q22IndependentLaw':'69ec6b7ec3b2429b77ca227dc1738c973080bd9d58a1958abf452d109381a1ff'}
req(r['direct_local_import_sha256']==require_imports,'original direct-local-import receipt changed')
for name,h in require_imports.items(): req(sha(HERE/'dependencies'/(name.split('.')[-1]+'.lean'))==h,'R402 dependency source mismatch')
cache=json.loads((HERE/'dependency-cache-identities.json').read_text())
req(cache['direct_imports']['AspisV8R19.R406SamplerWordDistribution']['source_sha256']=='b7b3aa0f3f42e39ce5945f3d4bdaad7544f2dfd39292ecf0bc26b9ea9eac1ed9','R406 supplemental source hash mismatch')
req(sha(HERE/'dependencies/R406SamplerWordDistribution.lean')==cache['direct_imports']['AspisV8R19.R406SamplerWordDistribution']['source_sha256'],'R406 supplemental source bytes mismatch')
# Verify saved inventories; exclude only each root inventory file itself.
files=json.loads((HERE/'FILES.json').read_text())
expected_files=sorted(p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p.name not in {'FILES.json','SHA256SUMS'})
req(files['files']==expected_files,'FILES.json mismatch')
rows=(HERE/'SHA256SUMS').read_text().splitlines()
for row in rows:
    digest,rel=row.split('  ',1); path=HERE/rel
    req(rel!='SHA256SUMS' and path.is_file() and sha(path)==digest,'checksum mismatch: '+rel)
req({row.split('  ',1)[1] for row in rows}=={p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file() and p.name!='SHA256SUMS'},'SHA256SUMS incomplete')
print(json.dumps({'status':'pass','target_sha256':EXPECTED,'run':rid,'axiom_names':expected_names,'foundation_set':sorted(FOUNDATIONS),'checked_files':len(expected_files)+1},indent=2))
