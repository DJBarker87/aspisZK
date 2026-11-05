from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent
pairs=[]
for base,count,label in [(6,9,'factored producer support'),(44,4,'S2 dispatch'),(52,4,'shared partial window'),(42,1,'shared partial control')]:
 for i in range(count):
  a,b=f'NHX_K{base+2*i:03}',f'NHX_K{base+2*i+1:03}'
  for name,expected,status in [(a,'VERIFICATION:- SUCCESSFUL',0),(b,'VERIFICATION:- FAILED',1)]:
   r=json.loads((E/name/'receipt.json').read_text());log=(E/name/'stdout.log').read_text()
   assert r['exit_status']==status and expected in log and 'timed out'not in log.lower()and'unwinding failures'not in log,(name,'nonqualifying')
   assert json.loads((E/(name+'-graph-check.json')).read_text())['graph_matches_frozen']
   assert json.loads((E/(name+'-lock-check.json')).read_text())['unchanged']
  pairs.append(dict(family=label,positive=a,corruption_control=b))
for n in[32,33]:
 log=(E/f'NHX_K{n:03}/stdout.log').read_text();assert 'VERIFICATION:- FAILED'in log and'timed out'not in log.lower()and'unwinding failures'not in log
patch=E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch'
assert hashlib.sha256(patch.read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
s=(E/'NHX_make_parents.py').read_text()
assert 'let f:[u8;2048]=kani::any()'in s
frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/weights.rs'],text=True)
assert 'if weights.variant==Variant::S2 && f.len()==64*32 {return s2_grouped_inactive_pair(f,low);}'in frozen
assert 'for s in 0..4 { partials[s]=partial_dot(f,common,s)?; }'in frozen
assert 'partials[s]=partial(f,common,s,l)?;Ok(())'in s
assert 'if weights.variant==Variant::S2 && f.len()==64*32 {return Some(child(f,low,l));}None'in s
allsource=s+'\n'+''.join(p.read_text()for p in E.glob('NHX_*.rs.txt'))
assert not re.search(r'\bstatic\s+(mut\s+)?\w+\s*:',allsource)
assert 'Option<fn'not in allsource and 'stub_verified'not in allsource
out=dict(status='PASS',pairs=pairs,arbitrary_message_qualified=True,zero_message_support_only=['NHX_K024..K031','NHX_K034..K041'],kmx_negative_controls=['NHX_K032','NHX_K033'],kmx_patch_sha256=hashlib.sha256(patch.read_bytes()).hexdigest(),no_writable_static=True,no_function_pointer=True,source_erasure_validated=True,source_association='NHX_SOURCE_ASSOCIATION.md',domain_history='NHX_DOMAIN_FINDING.md',copy_laws='retained KMX_CopyMeaning.lean and NHM/NHI encoding/frame laws',no_native_field_products=True)
(E/'NHX_NATIVE_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(pairs),'qualified native observation pairs; only two candidate rows')
