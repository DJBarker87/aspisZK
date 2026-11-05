from pathlib import Path
import subprocess,json,shlex,sys,hashlib,lzma,base64
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-pool-b4-20261107';a=sys.argv[1];assert a in ['NIE_E001','NIE_E002'] and not(E/a).exists()
source=(E/'NIE_kani_run.py').read_text();source=source[:source.index('# Per-run equality')]
source=source.replace("assert a.startswith('NIE_K') and 1<=int(a[5:])", "assert a in ['NIE_E001','NIE_E002']")
source=source.replace("assert sum((p/'receipt.json').exists() for p in E.glob('NIE_K[0-9][0-9][0-9]'))<120, 'Kani invocation budget exhausted'","assert sum((p/'receipt.json').exists() for p in E.glob('NIE_E[0-9][0-9][0-9]'))<2, 'Extraction budget exhausted'")
source=source.replace("for prior_patch in E.glob('NIE_K*-NIE_native.patch'):","for prior_patch in []:")
ns={'__file__':str(E/'NIE_kani_run.py')};exec(compile(source,'NIE_admit','exec'),ns);ssh=ns['ssh']
last=json.loads((E/max(p.name for p in E.glob('NIE_K[0-9][0-9][0-9].json'))).read_text());I=E.parent/'extract-stage-20261106'
leaf='pair_forest::decode_master_account' if a=='NIE_E001' else 'pair_forest::decode_lane_account_from_program_invariant_v1'
last.update(attempt=a,kind='extract',module=leaf,command=['python3','NIE_extract.py',a+'.json'],sources=['NIE_extract.py','NIE_kani_gate.py','NIE_RUST_SHA256.json','NIE_stage/NHR_stage.py','NIE_stage/NHR_STAGING_MANIFEST.json'],leaf_selector=leaf,extract_namespace='NIE_MasterExtract' if a=='NIE_E001' else 'NIE_LaneExtract',stager_sha256=hashlib.sha256((I/'NHR_stage.py').read_bytes()).hexdigest(),expected_time='NHR exact frozen staging/metadata, optimized Charon compilation, then one named Pool body translation; no arithmetic elimination',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
last['deps_fingerprint']['NHR_staging_inputs']={n:dict(path=str(I/n),sha256=hashlib.sha256((I/n).read_bytes()).hexdigest(),bytes=(I/n).stat().st_size) for n in ['NHR_stage.py','NHR_STAGING_MANIFEST.json','NHR_FROZEN_PAYLOAD.json.xz','NHR_FROZEN_PAYLOAD.json.sha256']}
files={a+'.json':json.dumps(last),'NIE_extract.py':(E/'NIE_extract.py').read_bytes(),'NIE_kani_gate.py':(E/'NIE_kani_gate.py').read_bytes()}
for n in ['NHR_stage.py','NHR_STAGING_MANIFEST.json','NHR_FROZEN_PAYLOAD.json.xz','NHR_FROZEN_PAYLOAD.json.sha256']:files['NIE_stage/'+n]=(I/n).read_bytes()
files={k:base64.b64encode(v.encode() if isinstance(v,str) else v).decode() for k,v in files.items()}
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r})
for n,t in json.loads({json.dumps(files)!r}).items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(t))
''');assert r.returncode==0,'Upload failure retained'
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True);(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});a={a!r}
names=[p for p in (b/a).rglob('*') if p.is_file()]+list((b/(a+'_extracted')).rglob('*'))+list(b.glob(a+'*json'))+[b/(a+'.llbc')]
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode() for p in names if p.is_file()}}))
''');assert r.returncode==0,'Recover read-only; never resubmit'
for n,v in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);raw=base64.b64decode(v)
 if n.endswith('.llbc') or len(raw)>20_000_000:p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:
  if '_extracted/' in n and n.endswith('.lean'):p=p.with_name(p.name+'.txt')
  p.write_bytes(raw)
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'}
with(E/'NIE_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
(E/'NIE_ACTIVE.json').unlink();print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}))
