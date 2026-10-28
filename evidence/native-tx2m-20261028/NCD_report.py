from pathlib import Path
import json,hashlib,re,subprocess,lzma
E=Path(__file__).resolve().parent
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NCD_[LK]*/receipt.json'))]
allowed={'propext','Classical.choice','Quot.sound'}
for r in receipts:
 assert {k:int(v) for k,v in r['limits'].items()}=={'memory.high':6442450944,'memory.max':8589934592,'memory.swap.max':0,'pids.max':64},r['attempt']
 if r['kind']=='lean' and r['exit_status']==0:
  for line in r['print_axioms']:
   m=re.search(r'axioms: \[(.*)\]',line)
   if m:assert set(x.strip() for x in m[1].split(',') if x.strip())<=allowed,(r['attempt'],line)
for p in E.glob('NCD_K*-graph-full.json.xz'):
 raw=lzma.decompress(p.read_bytes());h=hashlib.sha256(raw).hexdigest();assert h==(E/p.name.replace('.json.xz','.sha256')).read_text().strip();p.with_suffix('').with_suffix('.json.sha256').write_text(h+'\n')
neg=[];timeouts=[]
for r in receipts:
 if r['kind']=='kani':
  a=r['attempt'];s=(E/a/'stdout.log').read_text();g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen']
  assert (E/(a+'-lock-after.log')).read_text().strip()=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  if 'Failed Checks: assertion failed: b[15] == 0' in s:neg.append(a)
  if 'CBMC timed out' in s:timeouts.append(a)
lean=[r for r in receipts if r['kind']=='lean'];kani=[r for r in receipts if r['kind']=='kani'];ax=json.loads((E/'NCD_L199/receipt.json').read_text());assert ax['exit_status']==0 and len(ax['print_axioms'])==200
source_changes=subprocess.check_output(['git','diff','--name-only','4bb3b3f5','--','crates','programs'],text=True).splitlines();assert not source_changes,source_changes
result=dict(lean=dict(receipts=len(lean),pass_count=sum(r['exit_status']==0 for r in lean),rejected=sum(r['exit_status']!=0 for r in lean),unresolved_reserved=['NCD_L002','NCD_L006'],budget_used=len(lean)+2,ceiling=120),kani=dict(receipts=len(kani),positive_passes=sum(r['exit_status']==0 for r in kani),intended_negative_controls=neg,timeouts=timeouts,unresolved_reserved=['NCD_K004'],budget_used=len(kani)+1,ceiling=50),axioms=dict(target='NCD_AxiomsAll',attempt='NCD_L199',theorems=200,exit=ax['exit_status'],wall_seconds=ax['wall_seconds'],peak_rss_kib=ax['peak_rss_kib'],swaps=ax['swaps'],source_revision=ax['source_revision'],print_axioms=ax['print_axioms']),rust_frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',shipped_source_changes=source_changes,statuses={x:'OPEN' for x in ['U00','U07','U08','NativeFilled14759','NativeDigestRequests']},new_native_credit_depends_on_LPb_passing_stages=False)
assert result['kani']['budget_used']==50 and result['lean']['budget_used']<=120
(E/'NCD_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
compressed=[]
for p in sorted(E.rglob('*')):
 if p.is_file() and p.stat().st_size>20*1024*1024:
  data=p.read_bytes();dest=p.with_name(p.name+'.xz');dest.write_bytes(lzma.compress(data,preset=6));h=hashlib.sha256(data).hexdigest();p.with_name(p.name+'.sha256').write_text(h+'\n');assert lzma.decompress(dest.read_bytes())==data;compressed.append(dict(original=str(p.relative_to(E)),bytes=len(data),sha256=h,compressed=str(dest.relative_to(E))));p.unlink()
(E/'NCD_COMPRESSED_TRANSPORT.json').write_text(json.dumps(compressed,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['lean','kani','shipped_source_changes']},indent=2))
