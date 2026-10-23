"""Private, source-pinned per-step native gates; never whole-child harnesses."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2]; D=R/'docs/research/100bit-spend-path-20261013'; E=D/'evidence/s2k-20261023'; T=Path(__file__).parent
H='/home/dombarker/project-offloads/codex-cx-s2k-20261023'; HOST='dombarker@100.108.41.90'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def cut(path,start,end):
 text=(R/path).read_text();a=text.index(start);b=text.index(end,a);return text[a:b]
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
if sys.argv[1]=='prepare':
 p=E/'S2K-native';write(p/'Cargo.toml',(D/'evidence/s2i-20261023/S2I-native/Cargo.toml').read_text().replace('s2i-native-children','s2k-native-steps'))
 write(p/'src/statement.rs',(D/'evidence/s2i-20261023/S2I-native/src/statement.rs').read_text())
 # EXACT source statements, framed as one constructor-only step. No validation/syscall.
 ctor=cut('programs/r1-cost-probe/src/r1_pool_adapter.rs','    let result = PoolV1PairForestTerminalResultV1 {','    validate_pool_v1_pair_forest_terminal_result_against_statement_v1(statement, &result)')
 write(p/'src/S2K_construct.rs','fn construct(statement: &PoolV1PairForestTerminalStatementV1) -> PoolV1PairForestTerminalResultV1 {\n'+ctor+'    result\n}\n')
 # Exact private validator body and canonical predicate, with the original super module paths retained.
 valid=cut('crates/aspis-statement/src/pool_v1/pair_terminal.rs','fn validate_verified_afterstate(','pub fn encode_pool_v1_pair_verified_afterstate_v1(')
 canon=cut('crates/aspis-statement/src/pool_v1/pair_tree_profile.rs','pub(crate) fn digest_is_canonical(','\nimpl PoolV1PairLeafWitnessV1')
 write(p/'src/S2K_validate.rs',valid)
 write(p/'src/S2K_canonical.rs',canon)
 # The serializer's loop body, ONE ITERATION with arbitrary level/node/output.
 enc=cut('crates/aspis-statement/src/pool_v1/pair_terminal.rs','        let start = 48 + 32 * level;','    }\n    Ok(output)')
 write(p/'src/S2K_frontier_step.rs','fn frontier_step(mut output: [u8;688], level: usize, node: &aspis_statement::poseidon2::Digest) -> [u8;688] {\n'+enc+'    output\n}\n')
 mapping={'src/S2K_construct.rs':dict(source='programs/r1-cost-probe/src/r1_pool_adapter.rs',cut=ctor),'src/S2K_validate.rs':dict(source='crates/aspis-statement/src/pool_v1/pair_terminal.rs',cut=valid),'src/S2K_canonical.rs':dict(source='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs',cut=canon),'src/S2K_frontier_step.rs':dict(source='crates/aspis-statement/src/pool_v1/pair_terminal.rs',cut=enc)}
 for v in mapping.values():v['source_sha256']=sha(R/v['source']);v['cut_sha256']=hashlib.sha256(v['cut'].encode()).hexdigest()
 write(E/'source-cuts.json',json.dumps(mapping,indent=2)+'\n')
 files=(D/'evidence/s2i-20261023/native-files.txt').read_text().splitlines();write(E/'native-files.txt','\n'.join(files)+'\n')
 write(E/'native-source.json',json.dumps({f:dict(sha256=sha(R/f),bytes=(R/f).stat().st_size) for f in files},indent=2)+'\n')
 subprocess.run(['ssh',HOST,f'mkdir -p {H}/native-source'],check=True)
 subprocess.run(['rsync','-az','--files-from='+str(E/'native-files.txt'),str(R)+'/',HOST+':'+H+'/native-source/'],check=True)
 (E/'native-workspace.toml').write_bytes((D/'evidence/s2i-20261023/native-workspace.toml').read_bytes())
 subprocess.run(['scp',str(E/'native-workspace.toml'),HOST+':'+H+'/native-source/Cargo.toml'],check=True)
 for f in ['S2K_run_host.py','S2K_reservation.py']:subprocess.run(['scp',str(T/f),HOST+':'+H+'/'+f],check=True)
 sys.exit(0)
n=int(sys.argv[1]);target=sys.argv[2];assert target.startswith('S2K_') and 61<=n<=120;a=f'kani-{n:03d}';assert not (E/a).exists()
subprocess.run(['rsync','-az',str(E/'S2K-native')+'/',HOST+':'+H+'/S2K-native/'],check=True)
x=dict(attempt=a,kind='kani',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),command=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path','S2K-native/Cargo.toml','--target-dir','kani-target','-j','4','-Z','stubbing','-Z','function-contracts','-Z','unstable-options','--harness-timeout','120s','--exact','--harness',target,'--output-format','terse'],sources=[str(p.relative_to(E)) for p in sorted((E/'S2K-native').rglob('*')) if p.is_file()],timeout=180,env={'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS':'4','CARGO_NET_OFFLINE':'true','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0'},deps_fingerprint={'native_source_manifest_sha256':sha(E/'native-source.json'),'source_cuts_sha256':sha(E/'source-cuts.json'),'scope':'source-exact individual emitter/encoding steps; concrete levels use separately verified S2K_copy32 specialization of S2G_copy; no whole-function or success stub'},expected_time='optimized compilation then SAT for one named source step; no arithmetic elimination')
write(E/(a+'.json'),json.dumps(x,indent=2)+'\n');subprocess.run(['scp',str(E/(a+'.json')),HOST+':'+H+'/'+a+'.json'],check=True)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 S2K_reservation.py {a}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2K_run_host.py {a}.json'])
subprocess.run(['scp','-r',HOST+':'+H+'/'+a,str(E/a)],check=True);subprocess.run(['scp',HOST+':'+H+'/'+a+'-reservation.json',str(E)],check=True);sys.exit(r.returncode)
