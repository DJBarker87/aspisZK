from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2j-20261023'
H='/home/dombarker/project-offloads/codex-cx-s2j-20261023';HOST='dombarker@100.108.41.90'
a='kani-001';assert not (E/a).exists()
subprocess.run(['rsync','-az',str(E/'S2J-cut1')+'/',HOST+':'+H+'/S2J-cut1/'],check=True)
x=dict(attempt=a,kind='kani',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path','S2J-cut1/Cargo.toml','--target-dir','kani-target','-j','4','--exact','--harness','S2J_cut1_unbound_invocation','--output-format','terse'],sources=[str(p.relative_to(E)) for p in sorted((E/'S2J-cut1').rglob('*')) if p.is_file()],timeout=120,env={'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'4','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0'},deps_fingerprint={'scope':'first source guard only; native accounts.len projected; inherited CutRelated invocation blindness checked separately in Lean; no SDK/child reached'},expected_time='optimized tiny-crate compilation then constant cut1 relation diagnostic; no proof generation or elimination')
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n');subprocess.run(['scp',str(E/(a+'.json')),HOST+':'+H+'/'+a+'.json'],check=True)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 S2J_reservation.py {a}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2J_run_host.py {a}.json'])
subprocess.run(['scp','-r',HOST+':'+H+'/'+a,str(E/a)],check=True);subprocess.run(['scp',HOST+':'+H+'/'+a+'-reservation.json',str(E)],check=True)
sys.exit(r.returncode)
