from pathlib import Path
import json,hashlib,re,subprocess
p=Path(__file__).resolve().parent
r=next(x for x in p.parents if (x/'.git').exists())
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((p/'source-pin-coordinate-correction.json').read_text())
src=subprocess.check_output(['git','show',pins['revision']+':'+pins['path']],cwd=r)
assert sha(src)==pins['full_source_sha256']
for c in pins['cuts']:
 b=src[c['start_byte']:c['end_byte_exclusive']]
 assert sha(b)==c['sha256']
 assert (p/'extraction/input/fragments'/(c['name']+'.rs')).read_bytes()==b+b'\n'
clean=lambda s:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',s,flags=re.M)
raw=p/'extraction/generated/AspisR1M31Inverse'
assert (p/'sources/AspisR1M31Inverse/Types.lean').read_text()==clean((raw/'Types.lean').read_text())
s=clean((raw/'Funs.lean').read_text()).replace('import AspisR1M31Inverse.FunsExternal\n','')
for n in ['field.square_n_loop.body','field.square_n_loop','field.square_n']:
 s=s.replace('def '+n+'\n','def '+n+'\n  (mul : field.M31 → field.M31 → Result field.M31)\n')
s=s.replace('def field.M31.inv (self : field.M31)','def field.M31.inv (mul : field.M31 → field.M31 → Result field.M31) (self : field.M31)')
s=s.replace('field.M31.mul','mul').replace('field.square_n_loop.body iter1','field.square_n_loop.body mul iter1').replace('field.square_n_loop { start','field.square_n_loop mul { start').replace('field.square_n t','field.square_n mul t')
assert s==(p/'sources/M31InverseExplicitMul.lean').read_text()
old=(p/'dependencies/reused/ExtractedMaskForwardRange.lean').read_text()
new=(p/'sources/M31SquareRangeFacts.lean').read_text()
def fact(s,n):
 a=s.index('theorem '+n);z=s.find('\n\n',a)
 return s[a:z].strip()
assert fact(old,'next_done')==fact(new,'next_done')
assert fact(old,'next_step')==fact(new,'next_step')
m=json.loads((p/'manifest.json').read_text())
for x in m['modules']:
 f=p/x['source'];assert sha(f.read_bytes())==x['source_sha256']
 rc=json.loads((p/x['receipt']).read_text());assert rc['exit_status']==0 and rc['scope_swap_peak_bytes']==0
 log=(p/Path(x['receipt']).parent/'lean.log').read_text();assert 'sorryAx' not in log
 assert not re.search(r'(?m)^\s*(?:axiom|sorry)\b',f.read_text())
 assert not re.search(r'(?m)^set_option (?:maxHeartbeats|maxRecDepth)',f.read_text())
print('PASS: exact frozen byte cuts, explicit multiplication-only adapter, reused range proof text, selected green targets')
