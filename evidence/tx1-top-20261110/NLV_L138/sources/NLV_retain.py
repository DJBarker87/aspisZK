from pathlib import Path
import json,hashlib,lzma,shutil
B=Path.cwd();assert B.name=='codex-cx-tx1-top-20261110'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text())for p in sorted(B.glob('NLV_[LK][0-9][0-9][0-9]/receipt.json'))]
assert len([r for r in receipts if r['kind']=='kani'])==40
assert all(int(r['swaps'])==0 for r in receipts)
assert all(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}for r in receipts)
pins=json.loads((B/'NLV_SOURCE_PINS.json').read_text());assert all(H(B/'NLV_src'/n)==h for n,h in pins.items())
for n in range(1,41):
 a=f'NLV_K{n:03d}';g=json.loads((B/(a+'-graph-check.json')).read_text());l=json.loads((B/(a+'-lock-check.json')).read_text());c=json.loads((B/(a+'.json')).read_text())
 assert g['graph_matches_frozen']and l['unchanged']and l['before']==l['after']
 assert c['env']['CARGO_NET_OFFLINE']=='true'and c['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert '--locked'not in c['native_command']and all(f in c['metadata_features']for f in ['private-leaf-salts','optimized-terminal','program-build'])
selected=json.loads((B/'NLV_MODULES.json').read_text());sources=[]
for m,receipt in selected['selected_receipts'].items():
 p=B/'NLV_generated'/(m+'.lean');old=B/receipt;pinned=old.parent/'sources/NLV_generated'/(m+'.lean')
 assert p.read_bytes()==pinned.read_bytes(),m
 sources.append(dict(module=m,sha256=H(p),receipt=receipt))
# L121 completed all391 raw verdicts in178.275s, then packaging hit the
# unchanged180s outer cap. Complete ONLY lossless packaging; NEVER rerun walker.
repacked=[]
old=json.loads((B/'NLV_L121/receipt.json').read_text())
assert old['exit_status']==124
raw=json.loads((B/'NLV_audit/proof14/proof14.json').read_text())
expected=json.loads((B/'NLV_AUDIT_ROOTS.json').read_text())['groups'][14]
assert {r['root']for r in raw['results']}==set(expected)and len(raw['results'])==len(expected)
for p in B.glob('NEP_proof14_*'):
 if not p.is_file():continue
 blob=p.read_bytes();h=hashlib.sha256(blob).hexdigest();q=B/'NLV_audit/proof14'/(p.name+'.xz');sha=q.with_suffix('.sha256')
 valid=False
 if q.exists()and sha.exists():
  try:valid=hashlib.sha256(lzma.decompress(q.read_bytes())).hexdigest()==h and sha.read_text().strip()==h
  except lzma.LZMAError:pass
 if not valid:
  before=H(q)if q.exists()else None
  tmp=q.with_suffix('.xz.tmp');tmp.write_bytes(lzma.compress(blob,preset=0));tmp.replace(q);sha.write_text(h+'\n');repacked.append(dict(file=p.name,previous_compressed_sha256=before,completed_compressed_sha256=H(q),uncompressed_sha256=h))
(B/'NLV_PACKAGING_REPLACEMENT.json').write_text(json.dumps(dict(old_attempt='NLV_L121',old_exit=124,raw_results=len(raw['results']),raw_driver_exit=raw['exit_status'],raw_driver_wall=raw['wall_seconds'],replacement='NLV_L138 packaging only, no walker/proof rerun',repacked=repacked),indent=2))
pairs=0
for p in(B/'NLV_audit').rglob('*.xz'):
 q=p.with_suffix('.sha256')
 if q.exists():assert hashlib.sha256(lzma.decompress(p.read_bytes())).hexdigest()==q.read_text().strip();pairs+=1
native_tools=[]
candidates=[Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.cargo/bin/kani')]+list(Path('/home/dombarker/.kani/kani-0.67.0/bin').glob('*'))
for tool in candidates:
 if tool.is_file():native_tools.append(dict(path=str(tool),resolved=str(tool.resolve()),sha256=H(tool),bytes=tool.stat().st_size))
assert any(Path(x['path']).name=='cargo-kani'for x in native_tools)
(B/'NLV_NATIVE_TOOL_PINS.json').write_text(json.dumps(native_tools,indent=2))
size=sum(p.stat().st_size for p in B.rglob('*')if p.is_file())
assert size<30_000_000_000,size
out=dict(status='PASS',native_graphs=40,frozen_source_files=len(pins),compressed_sha_pairs=pairs,selected_sources=sources,own_host_bytes=size,own_limit_bytes=30_000_000_000,disk=shutil.disk_usage(B)._asdict(),deletions=0,target_retained=True,TMPDIR_retained=True,CARGO_TARGET_DIR=str(B/'NLV_target'),workspace=str(B))
(B/'NLV_RETENTION.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items()if k in ['status','native_graphs','frozen_source_files','compressed_sha_pairs','own_host_bytes','deletions']}))
