"""Validate this lane's receipts and pending overlay; does not replace NCZ."""
from pathlib import Path
import json,hashlib,tarfile,subprocess,re,collections
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
archive=json.loads((E/'NDI_RECEIPT_SOURCE_ARCHIVE.json').read_text())
assert sha((E/archive['archive']).read_bytes())==archive['archive_sha256']
tar=tarfile.open(E/archive['archive'],'r:xz')
final_pins=json.loads((E/'NDI_FINAL_PINS.json').read_text());assert not final_pins['selected_errors'] and not final_pins['final_source_errors']
records=[];native=[];refused=[];lean=[];extract=[]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for p in sorted(E.glob('NDI_*/receipt.json')):
 x=json.loads(p.read_text());a=x['attempt'];assert a==p.parent.name
 assert x['limits']==limits,(a,'limits')
 assert int(x['swaps'])==0,(a,'swap')
 for k in ['module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']:assert k in x,(a,k)
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 for n,h in x['source_hashes'].items():
  f=p.parent/'sources'/n
  data=f.read_bytes() if f.exists() else tar.extractfile(a+'/sources/'+n).read()
  assert sha(data)==h,(a,n)
 log=(p.parent/'stdout.log').read_text()
 if x['kind']=='kani':
  invoked='NDI_NATIVE_INVOCATION ' in log or 'Kani Rust Verifier' in log
  if invoked:
   native.append(x)
   for label in ['graph-check','source-check','lock-check']:
    q=json.loads((E/(a+'-'+label+'.json')).read_text())
    if label=='graph-check':
     assert q['graph_matches_frozen'] and q['all_crate_features'],a
     assert q['lock_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
    elif label=='lock-check':assert q['unchanged'],a
    else:assert not q['errors'],a
   assert x['env']['CARGO_NET_OFFLINE']=='true'
   assert x['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
   assert x['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
   assert '--harness-timeout' in x['native_command'] and x['native_command'][x['native_command'].index('--harness-timeout')+1]=='90s'
   if int(a[-3:])>=66:assert not json.loads((E/(a+'-source-postcheck.json')).read_text())['errors'],a
  else:
   refused.append(x);assert 56<=int(a[-3:])<=65 and x['exit_status']!=0,a
 elif x['kind']=='lean':
  lean.append(x);assert '-M7000' in x.get('lean_command',x['command'])
  check=E/(a+'-dependency-check.json')
  if check.exists():assert not json.loads(check.read_text())['errors'],a
  else:
   assert 1<=int(a[-3:])<=32 and x['command'][0].endswith('/lake'),a
   for path,pin in x['deps_fingerprint']['selected_objects'].items():
    assert final_pins['selected_objects_and_tools'][path]['sha256']==pin['sha256'],(a,path)

  if x['exit_status']==0:assert not any('sorryAx' in v for v in x['print_axioms']),a
 else:extract.append(x)
 summary={k:v for k,v in x.items() if k not in ['deps_fingerprint','env']}
 summary.update(deps_fingerprint_sha256=sha(json.dumps(x['deps_fingerprint'],sort_keys=True).encode()),full_receipt=a+'/receipt.json',full_receipt_sha256=sha(p.read_bytes()))
 records.append(summary)
assert len(native)==80 and len(refused)==10 and len(lean)<=80 and len(extract)<=20
positive=[1,3,5,8,10,12,16,18,20,29,30,33,37,38,42,43,47,67,69,71,73,74,77,79,81,83,85,87,89]
negative=[2,4,6,9,11,13,17,19,21,31,32,34,36,39,40,41,44,45,49,68,70,72,75,76,78,80,82,84,86,88,90]
for numbers,status,verdict in [(positive,0,'VERIFICATION:- SUCCESSFUL'),(negative,1,'VERIFICATION:- FAILED')]:
 for i in numbers:
  d=E/f'NDI_K{i:03}';x=json.loads((d/'receipt.json').read_text());log=(d/'stdout.log').read_text()
  assert x['exit_status']==status and verdict in log and 'CBMC timed out' not in log,(i,status)
assert set(positive).isdisjoint(negative)
proved=json.loads((E/'NDI_PROVEN_MODULES.json').read_text())
audit=json.loads((E/'NDI_L078/receipt.json').read_text());assert audit['exit_status']==0
actual=[re.search("'([^']+)'",v).group(1) for v in audit['print_axioms']]
assert sorted(actual)==proved['theorems']
assert Path('lean/NDI_Audit.lean').read_bytes()==(E/'NDI_L078/sources/NDI_generated/NDI_Audit.lean').read_bytes()
for v in audit['print_axioms']:
 assert set(re.findall(r'\[([^\]]*)\]',v)[0].replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'},v
for item in proved['modules']:
 p=E/item['receipt'];assert sha(p.read_bytes())==item['receipt_sha256']
 assert sha(Path(item['export']).read_bytes())==item['source_sha256']
assert not subprocess.check_output(['git','diff','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs']), 'shipped source changed'
changed=subprocess.check_output(['git','diff','--name-only','dff02f5b8b^'],text=True).splitlines()
assert all(n.startswith(('evidence/native-front3b-20261028/','lean/NDI_')) for n in changed),changed
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
delta=json.loads((E/'NDI_LEDGER_DELTA.json').read_text());ledger=json.loads((E/'NDI_LEDGER_UPDATED.json').read_text());assert ledger['NDI_pending_delta']==delta
assert len(delta['new_local_closures'])==5 and len({x['function'] for x in delta['new_local_closures']})==5 and delta['remaining_open']==13 and not delta['composed_closures']
matrix=(E/'NDI_FRONTIER_BRIDGES.md').read_text().splitlines();rows=[r for r in matrix if r.startswith('|`')];assert len(rows)==24
assert sum('|OPEN|' in r for r in rows)==13 and sum('|CLOSED-CONDITIONAL|' in r for r in rows)==11
assert 'report corpus changed' in (E/'NDI_NCZ_STAGE6.log').read_text()
(E/'NDI_ATTEMPTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in records))
result=dict(validation='PASS for own receipts/pending overlay only; official NCZ remains exit1 snapshot mismatch',kani_invocations=len(native),kani_validation_refusals=len(refused),lean=len(lean),extraction=len(extract),native_positive=len(positive),matched_negative=len(negative),native_timeout=sum('CBMC timed out' in (E/x['attempt']/'stdout.log').read_text() for x in native),native_other_errors=[x['attempt'] for x in native if int(x['attempt'][-3:]) not in positive+negative and 'CBMC timed out' not in (E/x['attempt']/'stdout.log').read_text()],peak_rss_kib=max(int(x['peak_rss_kib']) for x in records),swaps=0,axioms_top_theorems=len(actual),green_modules=len(proved['modules']),historical_direct_lean_pins_checked=32,postflight_selected_files=len(final_pins['selected_objects_and_tools']),shipped_equal_frozen=True,local_closures=11,new_local_closures=5,open=13,composed=0,attempt_index_sha256=sha((E/'NDI_ATTEMPTS.jsonl').read_bytes()))
(E/'NDI_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
