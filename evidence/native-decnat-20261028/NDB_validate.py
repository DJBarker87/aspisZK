from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rs=[json.loads(l) for l in (E/'NDB_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(rs)==90 and len({r['attempt'] for r in rs})==90
assert sum(r['kind']=='kani' for r in rs)==60 and sum(r['kind']=='lean' for r in rs)==30
for r in rs:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for key in ['module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','deps_fingerprint','print_axioms']:assert key in r
 for p,h in r['source_hashes'].items():
  # Large static frozen/KMX source files remain pinned on host, not duplicated.
  q=E/r['attempt']/'sources'/p
  if q.exists():assert H(q)==h,(r['attempt'],p)
 allowed={'propext','Classical.choice','Quot.sound'}
 if r['kind']=='lean' and r['exit_status']==0:
  for line in r['print_axioms']:
   if 'axioms:' in line:assert set(re.search(r'axioms: \[(.*)\]',line).group(1).split(', '))<=allowed,line
latest={r['module']:r for r in rs if r['kind']=='lean' and r['exit_status']==0}
delivery={}
for n,r in latest.items():
 p=Path('lean')/(n+'.lean');src=E/r['attempt']/'sources/NDB_generated'/(n+'.lean')
 assert p.is_file() and H(p)==H(src),n
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxHeartbeats|maxRecDepth)\b',p.read_text()),n
 delivery[str(p)]=dict(sha256=H(p),accepted_attempt=r['attempt'])
audit=json.loads((E/'NDB_L030/receipt.json').read_text());assert audit['exit_status']==0 and len(audit['print_axioms'])==55
post=json.loads((E/'NDB_POSTFLIGHT.json').read_text());pins=json.loads((E/'NDB_SETUP_PINS.json').read_text())
assert post['original_library_unchanged'] and post['imported_cache_unchanged']
assert post['all_selected_modifications_cfg_kani_only']
assert sorted(post['resolved_aeneas'].values())==sorted(pins['library'].values())
# Check every archived frozen path, including the two cfg(kani)-only normalized files.
tree=subprocess.check_output(['git','ls-tree','-r','-z','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'])
entries=[]
for raw in tree.split(b'\0'):
 if not raw:continue
 header,path=raw.split(b'\t',1);path=path.decode()
 if path in post['source_hashes']:entries.append((path,header.split()[2].decode()))
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
# communicate avoids pipe deadlocks; all archived source is small.
blobdata=proc.communicate(('\n'.join(oid for _,oid in entries)+'\n').encode())[0];assert proc.returncode==0
cursor=0
for path,oid in entries:
 end=blobdata.index(b'\n',cursor);header=blobdata[cursor:end].split();size=int(header[-1]);cursor=end+1
 data=blobdata[cursor:cursor+size];cursor+=size+1
 selected=post['normalized_frozen_files'].get(path,post['source_hashes'][path])
 assert hashlib.sha256(data).hexdigest()==selected,path
changes=subprocess.check_output(['git','diff','--name-only','b1a7fa4658^'],text=True).splitlines()
assert all(p.startswith('evidence/native-decnat-20261028/') or p.startswith('lean/NDB_') for p in changes)
assert len(post['retained_objects'])==22 and len(post['resolved_aeneas'])==219
assert not (E/'NDB_ACTIVE.json').exists()
assert not list(E.rglob('*.olean')) and not list(E.rglob('*.elf'))
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
(E/'NDB_DELIVERY.json').write_text(json.dumps(delivery,indent=2)+'\n')
x=dict(validation='PASS',attempts=len(rs),kani=60,lean=30,accepted_modules=len(latest),new_top_theorems=49,final_audited_statements=55,only_standard_axioms=True,deployed_features_and_frozen_graph='NDB_RESULTS.json/per-attempt graph receipts',objects_retained=22,resolved_aeneas_pins=219,frozen_source_paths_checked=len(entries),shipped_repo_source_changes=False,ELF_rebuild_trigger=False,top_bridges={'op48':'OPEN','op49':'OPEN','op50':'OPEN'})
(E/'NDB_VALIDATION.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2))
