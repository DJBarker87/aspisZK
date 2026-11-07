"""Read-only mismatch diagnosis plus copies into PCH cache only."""
import pathlib,subprocess,json,hashlib,sys,shutil
B=pathlib.Path(__file__).resolve().parent;a=sys.argv[1];tool=pathlib.Path('/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin');old=pathlib.Path('/home/dombarker/project-offloads/codex-cx-legacy-removal-20261109/pool2')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert shutil.disk_usage(B).free>=40_000_000_000
out={}
for n,p in [('retained',old/'artifacts/aspis_pool.so'),('new',B/'PCH_B001/aspis_pool.so'),('new_unstripped',B/'PCH_B001/libaspis_pool.so')]:
 out[n]=dict(sha256=sha(p),bytes=p.stat().st_size)
 for arg in ['--sections','--symbols','--file-header']:
  r=subprocess.run([str(tool/'llvm-readelf'),arg,str(p)],capture_output=True,text=True);out[n][arg]=r.stdout
 q=B/('PCH_'+n+'.so')
 if not q.exists():shutil.copyfile(p,q)
for name in ['aspis_pool.command.json','aspis_pool.mono.txt']:
 p=old/'diagnostics'/name;q=B/('PCH_retained_'+name);shutil.copyfile(p,q);out[name]=dict(sha256=sha(q),source=str(p))
# Exact cargo-build-sbf source reveals its postprocessing and environment.
r=subprocess.run(['bash','-c','rg -n "objcopy|strip|remap|linker|RUSTFLAGS|RUSTC|PATH|platform_tools" /home/dombarker/.cargo/registry/src/*/solana-cargo-build-sbf-*/src/main.rs'],capture_output=True,text=True);out['cargo_sbf_source_search']=r.stdout
(B/(a+'_DIAGNOSIS.json')).write_text(json.dumps(out,indent=1))
print('PCH ELF section/symbol mismatch audit recorded')
