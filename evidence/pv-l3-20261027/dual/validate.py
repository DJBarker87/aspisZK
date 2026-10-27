#!/usr/bin/env python3
"""Check retained source/PC/receipt associations, never claim CT correctness."""
from pathlib import Path
import json,re,hashlib,subprocess
O=Path(__file__).resolve().parent
def read(p):return json.loads((O/p).read_text())
a=read('A/receipt.json');b=read('B/receipt.json');e=read('A/extraction.json');post=read('post-build-validation.json');cleanup=read('cleanup.json');f=read('findings.json');d=read('source-differences.json')
assert a['exit_status']==0 and b['exit_status']==101 and 'binary_sha256' not in b
assert a['binary_sha256']==e['binary_sha256']==cleanup['retained_A_binary_sha256']==f['A_sha256']
assert e['full_disassembly_sha256']==cleanup['retained_full_disassembly_sha256']
assert a['binary_bytes']==2495136 and b['source_revision'].startswith('237e135561')
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in [a,b,e,post]:
 assert r['limits']==limits and r['cgroup_swap_peak_bytes']==0
for name in ['A','B']:
 assert not post[name]['mismatches']
 assert post[name]['source_revision']==read(name+'-source.json')['revision']
assert all(x['removed'] for x in cleanup['cargo_targets'])
assert len(d['differing'])==26 and len(d['missing'])==6
pins=json.loads((O.parent/'shipped/client-pins.json').read_text());ap=read('A-source.json')['files'];bp=read('B-source.json')['files']
assert pins['files']==ap
assert [x['path'] for x in d['differing']]==[p for p in pins['files'] if p in bp and ap[p]!=bp[p]]
assert [x['path'] for x in d['missing']]==[p for p in pins['files'] if p not in bp]
pcs={}
for line in (O/'A/selected-disassembly.txt').read_text().splitlines():
 m=re.match(r'\s*([0-9a-f]+): (.*)',line)
 if m:pcs['0x'+m[1]]=m[2]
assert len(f['findings'])==15
for r in f['findings']:
 assert r['B'] is None and r['B_reason']
 src=subprocess.check_output(['git','show',r['source_revision']+':'+r['path']],text=True).splitlines()
 for x in r['source_context']:assert src[x['line']-1]==x['text']
 for x in r['A']:assert pcs[x['address']]==x['instruction']
assert [pcs[p].split()[0] for p in ['0xbd6a0','0xbd6a6','0xbd6ac']]==['jne']*3
counter=read('pole-prefix-counterexample.json');assert counter['chi']!=counter['slot_early'] and counter['chi']!=counter['slot_late']
assert counter['chi'][0]!=counter['slot_early'][0] and counter['chi'][0]==counter['slot_late'][0]
metrics=[]
for name in ['A','B']:
 rec=read(name+'/receipt.json');tim=(O/name/'time.log').read_text()
 def get(key):
  m=re.search(re.escape(key)+r':\s*(\d+)',tim);return int(m[1]) if m else None
 metrics.append(dict(target=rec['target'],artifact=name,source_revision=rec['source_revision'],exit_status=rec['exit_status'],wall_seconds=rec['wall_seconds'],peak_rss_kib=get('Maximum resident set size (kbytes)'),swaps=get('Swaps'),cgroup_peak_bytes=rec['cgroup_memory_peak_bytes'],print_axioms=rec['print_axioms']))
for file,timefile in [('A/extraction-initial.json',None),('A/extraction.json','A/extract-time.log'),('post-build-validation.json','verify-time.log')]:
 rec=read(file);tim=(O/timefile).read_text() if timefile else '';m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tim)
 metrics.append(dict(target=rec['target'],source_revision=rec.get('source_revision',a['source_revision'] if file.startswith('A/') else {'A':a['source_revision'],'B':b['source_revision']}),exit_status=rec['exit_status'],wall_seconds=rec['wall_seconds'],peak_rss_kib=int(m[1]) if m else None,peak_rss_note='GNU time' if m else 'not captured for initial extraction; cgroup memory peak retained, not relabelled RSS',cgroup_peak_bytes=rec['cgroup_memory_peak_bytes'],swap_peak_bytes=rec['cgroup_swap_peak_bytes'],print_axioms=rec['print_axioms']))
(O/'resource-summary.json').write_text(json.dumps(metrics,indent=2)+'\n')
out=dict(status='PASS retained evidence consistency only',A=a['binary_sha256'],B='BUILD FAILED --locked exit 101; no binary',source_files_A=len(ap),source_files_B=len(bp),changed=26,missing=6,findings=15,new_finding_groups=8,V373='OPEN / P; incomplete transitive two-artifact audit',V374='OPEN / P; proposed plan, no samples',Lean_attempts=0,Kani_attempts=0,print_axioms='N/A (no Lean)',cargo_targets_removed=True)
(O/'validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
