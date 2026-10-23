from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert p.is_file() and p.stat().st_size==f['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256']
t=m['targets'][0];assert t['exit_status']==0 and t['process_swaps']==0 and t['scope_swap_peak_bytes']==0
assert hashlib.sha256((r/'sources/S9ReverseRangeProgressV1.lean').read_bytes()).hexdigest()==t['source_sha256']
log=(r/'proof/lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
rep=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S);assert len(rep)==3
for n,a in rep:assert {x.strip() for x in a.split(',')}<={'propext','Classical.choice','Quot.sound'}
a=json.loads((r/'proof/admission-summary.json').read_text());assert all(a['checks'].values()) and a['scope_high_bytes']==5*1024**3//2 and a['scope_max_bytes']==7*1024**3//2 and a['swap_max_bytes']==0
src=(r/'sources/S9ReverseRangeProgressV1.lean').read_text();old=(r/'history/failed-eof-v1/S9ReverseRangeProgressV1.lean').read_text();assert src==old.replace('end AspisR1S9ReverseRangeProgressV1','end\nend AspisR1S9ReverseRangeProgressV1')
origin=(r/'source-origin/R306BatchReverseStepExecution.reference.lean').read_text();a=origin.index('abbrev ReverseRange :=');b=origin.index('\ntheorem body2_done',a);x=src.index('abbrev ReverseRange :=');y=src.index('\ntheorem reverse_next_some_progress',x);assert origin[a:b].strip()==src[x:y].strip()
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.pyc','.so','.dylib','.dll'}
print('PASS: source-only reverse-range packet, exact R306 proof reuse, current exit0/std3, guarded resources, failed EOF predecessor preserved')
