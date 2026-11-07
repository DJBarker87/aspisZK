from pathlib import Path
import json,hashlib,re,lzma,subprocess
E=Path(__file__).resolve().parent;H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];sources=0
for kind,count in [('L',140),('K',40)]:
 for j in range(1,count+1):
  a=f'NLZ_{kind}{j:03}';p=E/a/'receipt.json';r=json.loads(p.read_text());assert r['attempt']==a
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert int(r['swaps'])==0
  ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed']is True
  disks=sorted(E.glob(a+'-disk-*.json'),key=lambda p:int(p.stem.rsplit('-',1)[1]));assert json.loads(disks[-1].read_text())['free']>=40_000_000_000
  for n,h in r['source_hashes'].items():assert H(p.parent/'sources'/n)==h,(a,n);sources+=1
  receipts.append(r)
assert len({r['attempt']for r in receipts})==180
m=json.loads((E/'NLZ_MODULES.json').read_text());axioms=[]
for name,rc in m['selected_receipts'].items():
 p=E/rc;r=json.loads(p.read_text());n='NLZ_generated/'+name+'.lean';assert r['exit_status']==0 and H(E/n)==r['source_hashes'][n]
 for line in r['print_axioms']:
  if 'depends on axioms:'in line:
   names=line.split('[',1)[1].rsplit(']',1)[0].split(', ');assert set(names)<={'propext','Classical.choice','Quot.sound'},line
  axioms.append(line)
assert len(axioms)==24
assert '_private'in (E/'NLZ_AUDIT_ROOTS.json').read_text() or json.loads((E/'NLZ_AUDIT_ROOTS.json').read_text())['roots']
assert '_private'not in(E/'NLZ_COMBINED_IMPORT.lean').read_text()
a=json.loads((E/'NLZ_AUDIT.json').read_text());assert a['raw_all_standard']and a['raw_roots']==11697 and a['scan_modules']==17264
assert {r['root']for r in a['collector_disagreements']}=={'AspisR1.NKR_ScheduleExt.transition','NHC_DecodeModel.decoder_error'}
assert json.loads((E/'NLZ_FINAL.json').read_text())['status']=='PASS_FINAL_RETENTION'
assert not(E/'NLZ_CLIENT_ACTIVE').exists()
assert not subprocess.check_output(['git','diff','--name-only','--','crates','programs','Cargo.lock'],text=True).strip()
large=[str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20*1024*1024];assert not large,large
out=dict(status='PASS',receipts=180,lean_support=140,kani=40,source_snapshots=sources,active_modules=len(m['modules']),new_top_roots=24,raw_roots=11697,full_combined_audits=1,peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),swaps=0,closed_rows=[],qualified_rows=[],target_established=False,full_resource_packets=False)
(E/'NLZ_VALIDATION.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
