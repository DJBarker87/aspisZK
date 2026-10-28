from pathlib import Path
import hashlib,json,shutil,os,urllib.request,tomllib
b=Path(__file__).resolve().parent
hashfile=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
# Recover the exact source that failed before the helper repair.
(b/'KNH_N040_source.rs.txt').write_bytes((b/'KNH_N040/sources/KNH_scratch/KNH_probe.rs').read_bytes())
(b/'KNH_INSTALL_source.py.txt').write_bytes((b/'KNH_INSTALL/sources/KNH_install.py').read_bytes())
pinned={str(p):hashfile(p) for p in Path('/home/dombarker/.kani/kani-0.67.0/bin').iterdir() if p.is_file()}
pinned['/home/dombarker/.cargo/bin/cargo-kani']=hashfile(Path('/home/dombarker/.cargo/bin/cargo-kani'))
cache_manifest=json.loads((b/'KNH_CACHE_IMPORT.json').read_text());cache=Path(cache_manifest['destination'])
cache_bad=[n for n,pin in cache_manifest['files'].items() if not (cache/n).is_file() or hashfile(cache/n)!=pin['sha256']]
assert not cache_bad,cache_bad
install=json.loads((b/'KNH_INSTALL_FILES.json').read_text());root=b/'KNH_install'
install_bad=[n for n,pin in install.items() if not (root/n).is_file() or hashfile(root/n)!=pin['sha256']]
assert not install_bad,install_bad
links={str(p.relative_to(root)):os.readlink(p) for p in root.rglob('*') if p.is_symlink()}
# Download provenance metadata only; no tool is installed or modified here.
url='https://static.rust-lang.org/dist/2026-08-21/channel-rust-nightly.toml'
data=urllib.request.urlopen(url).read();manifest=tomllib.loads(data.decode());target='x86_64-unknown-linux-gnu'
components={n:manifest['pkg'][n]['target'][target] for n in ['cargo','rustc','rust-std']}
(b/'KNH_TOOLCHAIN_PROVENANCE.json').write_text(json.dumps(dict(manifest_url=url,manifest_sha256=hashlib.sha256(data).hexdigest(),components=components),indent=2)+'\n')
removed=[]
for n in ['KNH_target_new','KNH_target_old','KNH_metadata_target','KNH_tmp']:
 p=b/n
 if p.exists():shutil.rmtree(p);removed.append(str(p))
# No own live worker/prover may remain. Exclude this audit's own command chain.
live=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:args=(p/'cmdline').read_bytes().split(b'\0');exe=args[0].decode();cmd=b' '.join(args).decode()
 except (OSError,UnicodeDecodeError,IndexError):continue
 if ('/kani-driver' in exe or exe in ['cbmc','goto-instrument','goto-cc']) and str(b) in cmd:live.append(dict(pid=int(p.name),command=cmd))
assert not live,live
out=dict(pinned_tools=pinned,imported_cache_files=len(cache_manifest['files']),cache_unchanged=True,cache_retained=str(cache),installed_regular_files=len(install),installation_unchanged=True,installation_retained=str(root),installed_symlinks=links,removed=removed,live_own_provers=live,disk_free_bytes=shutil.disk_usage(b).free)
(b/'KNH_CLEANUP.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
