"""Capture immutable upstream rust-src matching Kani's exact rustc commit.
The old toolchain has no installed rust-src. No tool or sysroot is installed or
changed: source files are fetched into this job's evidence cache only.
"""
from pathlib import Path
import json,lzma,subprocess,re,hashlib,urllib.request,time
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028');R=H/'resume17';O=R/'std-sources';O.mkdir(exist_ok=True)
version=subprocess.check_output(['/home/dombarker/.kani/kani-0.67.0/toolchain/bin/rustc','-vV'],text=True);commit=re.search(r'commit-hash: (\w+)',version)[1];assert commit.startswith('53732d5e0')
deployed=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
rows=[];files={}
for group in ['host-mask','statement-mask','reconstruct','transition','external','internal']:
 d=R/('std-'+group);idx=json.loads((d/'index.json').read_text())
 for record in idx['records']:
  f=Path(record['symbol_dump']);raw=json.loads(lzma.open(f).read())
  for block in raw:
   for key,v in block.get('symbolTable',{}).items():
    if v.get('type',{}).get('id')!='code':continue
    loc=v.get('location',{});path=loc.get('file','');name=v.get('prettyName',key)
    if '/library/' not in path:continue
    rel=path.split('/library/',1)[1]
    if not rel.startswith(('core/','std/','alloc/')):continue
    rows.append(dict(group=group,harness=record['harness']['pretty_name'],symbol=key,name=name,location=loc,source=rel,has_body=bool(v.get('prettyValue','')),symbol_dump=str(f),symbol_dump_sha256=record['symbol_dump_sha256']))
    if rel in files:continue
    out=O/rel;out.parent.mkdir(parents=True,exist_ok=True);p=deployed/rel
    url=f'https://raw.githubusercontent.com/rust-lang/rust/{commit}/library/{rel}'
    try:
     if not out.with_suffix(out.suffix+'.kani').exists():
      data=urllib.request.urlopen(url,timeout=30).read();out.with_suffix(out.suffix+'.kani').write_bytes(data)
     data=out.with_suffix(out.suffix+'.kani').read_bytes()
     dep=p.read_bytes();out.with_suffix(out.suffix+'.deployed').write_bytes(dep)
     files[rel]=dict(kani_source_url=url,kani_source_sha256=hashlib.sha256(data).hexdigest(),deployed_path=str(p),deployed_source_sha256=hashlib.sha256(dep).hexdigest(),kani_path=str(out.with_suffix(out.suffix+'.kani')),deployed_capture=str(out.with_suffix(out.suffix+'.deployed')))
    except Exception as e:files[rel]=dict(error=str(e),url=url)
(R/'std-reached.json').write_text(json.dumps(dict(actual_bundled_rustc=version,compiler_commit=commit,source_recovery='Exact upstream compiler commit; bundled toolchain has no installed rust-src; no toolchain modified',rows=rows,files=files,method='All code-typed entries, including declarations without bodies, from each selected proof-harness symtab. No source-grep reachability inference.'),indent=2)+'\n')
print(json.dumps(dict(items=len(rows),files=len(files),errors=[p for p,v in files.items()if 'error'in v])))
