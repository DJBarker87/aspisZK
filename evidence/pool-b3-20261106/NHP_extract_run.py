from pathlib import Path
import subprocess,json,shlex,sys,hashlib,lzma
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-pool-b3-20261106';a=sys.argv[1];assert a in ['NHP_E001','NHP_E002'] and not(E/a).exists()
# Reuse the native client's transport/admission protocol, without launching Kani.
source=(E/'NHP_kani_run.py').read_text();source=source[:source.index('# Per-run equality')]
source=source.replace("a=sys.argv[1];harness=sys.argv[2] if len(sys.argv)>2 else 'pair_forest_dispatch::NFO_read::association';assert __import__('re').fullmatch(r'[A-Za-z_][A-Za-z_0-9:]++',harness);assert a.startswith('NHP_K') and 1<=int(a[5:])<=120", "a=sys.argv[1]")
source=source.replace("for prior_patch in E.glob('NHP_K*-NHP_native.patch'):","for prior_patch in []:")
ns={'__file__':str(E/'NHP_kani_run.py')};exec(compile(source,'NHP_admit','exec'),ns);ssh=ns['ssh']
last=json.loads((E/'NHP_K026.json').read_text());last.update(attempt=a,kind='extract',module='Frozen Pool decoder leaves',command=['python3','NHP_extract.py',a+'.json'],sources=['NHP_extract.py','NHP_kani_gate.py','NHP_RUST_SHA256.json'],leaf_selectors=['NHP_reference::transaction_level'],extract_namespace='NHP_StackRef',expected_time='optimized dependency compilation then named opaque-callee MIR/Aeneas leaf extraction; no arithmetic elimination',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
files={a+'.json':json.dumps(last),'NHP_extract.py':(E/'NHP_extract.py').read_text()}
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
with(E/'NHP_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
(E/'NHP_ACTIVE.json').unlink();print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}))
