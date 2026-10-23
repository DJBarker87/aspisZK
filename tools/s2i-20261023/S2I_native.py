from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2i-20261023';H='/home/dombarker/project-offloads/codex-cx-s2i-20261023';HOST='dombarker@100.108.41.90'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if sys.argv[1]=='prepare':
 p=E/'S2I-native';(p/'src').mkdir(parents=True,exist_ok=True)
 (p/'Cargo.toml').write_text('''[package]
name = "s2i-native-children"
version = "0.1.0"
edition = "2021"
[workspace]
[dependencies]
aspis-statement = { path = "../native-source/crates/aspis-statement", features = ["r0", "pool-v1-kernel"] }
aspis-core = { path = "../native-source/crates/aspis-core", features = ["r0"] }
solana-program-error = "=2.2.2"
[profile.dev]
opt-level = 3
debug = 0
[profile.release]
opt-level = 3
''')
 src=(R/'programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text();body=src[src.index('fn emit_result('):src.index('\n#[inline(never)]\nfn stage1')]
 (p/'src/S2I_emit.rs').write_text(body+'\n')
 (p/'src/statement.rs').write_bytes((D/'evidence/s2c-20261023/kani-native/src/statement.rs').read_bytes())
 files=(D/'evidence/s2c-20261023/native-files.txt').read_text().splitlines()
 (E/'native-files.txt').write_text('\n'.join(files)+'\n');(E/'native-source.json').write_text(json.dumps({f:dict(sha256=sha(R/f),bytes=(R/f).stat().st_size) for f in files},indent=2)+'\n')
 subprocess.run(['ssh',HOST,f'mkdir -p {H}/native-source'],check=True)
 subprocess.run(['rsync','-az','--files-from='+str(E/'native-files.txt'),str(R)+'/',HOST+':'+H+'/native-source/'],check=True)
 (E/'native-workspace.toml').write_bytes((D/'evidence/s2c-20261023/native-workspace.toml').read_bytes())
 subprocess.run(['scp',str(E/'native-workspace.toml'),HOST+':'+H+'/native-source/Cargo.toml'],check=True)
 sys.exit(0)
n=int(sys.argv[1]);target=sys.argv[2];assert target.startswith('S2I_') and 1<=n<=60;a=f'kani-{n:03d}';assert not (E/a).exists()
subprocess.run(['rsync','-az',str(E/'S2I-native')+'/',HOST+':'+H+'/S2I-native/'],check=True)
x=dict(attempt=a,kind='kani',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path','S2I-native/Cargo.toml','--target-dir','kani-target','-j','4','-Z','stubbing','-Z','unstable-options','--harness-timeout','120s','--exact','--harness',target,'--output-format','terse'],sources=[str(p.relative_to(E)) for p in sorted((E/'S2I-native').rglob('*')) if p.is_file()],timeout=180,env={'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'4','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0'},deps_fingerprint={'native_source_manifest':sha(E/'native-source.json'),'scope':'verbatim emit_result body; runtime set_return_data semantics explicit; no SDK native allocation port'},expected_time='optimized compilation then native emit validation/encoding control SAT; no finite-field elimination')
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n');subprocess.run(['scp',str(E/(a+'.json')),HOST+':'+H+'/'+a+'.json'],check=True)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 S2I_reservation.py {a}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2I_run_host.py {a}.json'])
subprocess.run(['scp','-r',HOST+':'+H+'/'+a,str(E/a)],check=True);subprocess.run(['scp',HOST+':'+H+'/'+a+'-reservation.json',str(E)],check=True);sys.exit(r.returncode)
