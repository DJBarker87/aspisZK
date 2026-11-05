from pathlib import Path
import subprocess,json,shlex,sys,hashlib,lzma
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-pool-leaves-20261105';a=sys.argv[1];assert a in ['NHC_E001','NHC_E002'] and not(E/a).exists()
# Reuse the native client's transport/admission protocol, without launching Kani.
source=(E/'NHC_kani_run.py').read_text();source=source[:source.index('# Per-run equality')]
source=source.replace("a=sys.argv[1];harness=sys.argv[2] if len(sys.argv)>2 else 'pair_forest_dispatch::NFO_read::association';assert __import__('re').fullmatch(r'[A-Za-z_][A-Za-z_0-9:]++',harness);assert a.startswith('NHC_K') and 1<=int(a[5:])<=120", "a=sys.argv[1]")
source=source.replace("for prior_patch in E.glob('NHC_K*-NHC_native.patch'):","for prior_patch in []:")
ns={'__file__':str(E/'NHC_kani_run.py')};exec(compile(source,'NHC_admit','exec'),ns);ssh=ns['ssh']
last=json.loads((E/'NHC_K002.json').read_text());last.update(attempt=a,kind='extract',module='Frozen Pool decoder leaves',command=['python3','NHC_extract.py',a+'.json'],sources=['NHC_extract.py','NHC_kani_gate.py','NHC_RUST_SHA256.json'],leaf_selectors=['pair_forest::split_pair_forest_terminal_bump_hints_v1','pair_forest::decode_terminal_request_box_v1','pair_forest::decode_terminal_master_box_v1','pair_forest::decode_terminal_checkpoint_box_v1','pair_forest::decode_terminal_lane_box_v1'] if a=='NHC_E001' else ['pair_forest::split_pair_forest_terminal_bump_hints_v1'],extract_namespace='NHC_Production' if a=='NHC_E001' else 'NHC_Hints',expected_time='optimized dependency compilation then named opaque-callee MIR/Aeneas leaf extraction; no arithmetic elimination',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
files={a+'.json':json.dumps(last),'NHC_extract.py':(E/'NHC_extract.py').read_text()}
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r})
for n,t in json.loads({json.dumps(files)!r}).items():(b/n).write_text(t)
''');assert r.returncode==0,r.stderr
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True);(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});a={a!r}
names=[p for p in (b/a).rglob('*') if p.is_file()]+list((b/(a+'_extracted')).rglob('*'))+list(b.glob(a+'*json'))+[b/(a+'.llbc')]
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode() for p in names if p.is_file()}}))
''');assert r.returncode==0,r.stderr
import base64
for n,v in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);raw=base64.b64decode(v)
 if n.endswith('.llbc') or len(raw)>20_000_000:p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:
  if '_extracted/' in n and n.endswith('.lean'):p=p.with_name(p.name+'.txt')
  p.write_bytes(raw)
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items() if k!='deps_fingerprint'}
with(E/'NHC_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
(E/'NHC_ACTIVE.json').unlink();print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}))
