from pathlib import Path
import json,hashlib,shutil,os,subprocess,tomllib
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');source=json.loads((D/'runtime-source-pins.json').read_text());bad=[]
for x in source['files']:
 p=D/'src'/x['path'];actual=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
 if actual!=x['sha256']:bad.append(dict(path=x['path'],expected=x['sha256'],actual=actual))
assert not bad,bad
live=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:argv=(p/'cmdline').read_bytes().split(b'\0');args=b' '.join(argv).decode(errors='replace')
 except (PermissionError,FileNotFoundError,ProcessLookupError):continue
 if str(D) in args and any(Path(a.decode(errors='replace')).name in ['cargo','rustc','kani-compiler','cbmc','charon'] for a in argv if a):live.append(dict(pid=p.name,args=args))
assert not live,live
removed=[]
for p in [D/'target',*D.glob('library-target-*')]:
 if p.exists():
  assert p.parent==D and (p.name=='target' or p.name.startswith('library-target-'))
  shutil.rmtree(p);removed.append(str(p))
versions={}
for tc in ['1.94.1','nightly-2026-06-01','1.89.0-sbpf-solana-v1.52']:
 versions[tc]={tool:subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run',tc,tool,'-vV' if tool=='rustc' else '--version'],text=True).strip() for tool in ['rustc','cargo']}
configs=[]
for p in [Path('/home/dombarker/.cargo/config.toml'),Path('/home/dombarker/.cargo/config')]:
 if p.exists():
  a=tomllib.loads(p.read_text());configs.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),build=a.get('build'),profile=a.get('profile'),target_flags={k:{x:y for x,y in v.items() if x in ['rustflags','linker','runner']} for k,v in a.get('target',{}).items()},relevant_env={k:v for k,v in a.get('env',{}).items() if k=='RUSTFLAGS' or k.startswith('CARGO_PROFILE_')}))
result=dict(tool_versions=versions,cargo_configuration=configs,source_revision=source['revision'],runtime_files_verified=len(source['files']),source_mismatches=bad,live_own_compilers=live,removed_rebuildable_targets=removed,retained='all source inputs, text MIR, hashes, metadata, scope receipts; no task wallet/account key was created or removed')
(D/'cleanup.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
