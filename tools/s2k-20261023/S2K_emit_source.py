"""Extract both emitter prefixes up to their actual return-data call."""
from pathlib import Path
import ast,hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2k-20261023';T=Path(__file__).parent
HOST='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-cx-s2k-20261023';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
phase=sys.argv[1]
if phase=='prepare':
 P=E/'S2K-emit';(P/'src').mkdir(parents=True,exist_ok=True)
 code='#![allow(non_snake_case)]\nuse aspis_statement::pool_v1::*;\nuse solana_program_error::ProgramError;\n';cuts=[]
 for file,fun,name in [('programs/r1-cost-probe/src/r1_pool_adapter.rs','emit_result','S2K_probe_prefix'),('programs/aspis-verifier/src/v7_pair_forest_dispatch.rs','emit_result_v1','S2K_verifier_prefix')]:
  s=(R/file).read_text();a=s.index('fn '+fun+'(');a=s.index('{',a)+1;b=s.index('    program::set_return_data(&encoded);',a);prefix=s[a:b]
  code+='\npub fn '+name+'(statement: &PoolV1PairForestTerminalStatementV1) -> Result<[u8;792],ProgramError> {'+prefix+'    Ok(encoded)\n}\n'
  cuts.append(dict(source=file,source_sha256=sha(R/file),native_function=fun,extracted_function=name,prefix=prefix,prefix_sha256=hashlib.sha256(prefix.encode()).hexdigest(),reached_call='program::set_return_data(&encoded);',suffix='    Ok(())',adaptation='Only function name/return carrier changed; original pre-syscall statements are byte-identical. Exact pending call argument is returned, NOT an event or a syscall-success observation.'))
 (P/'src/lib.rs').write_text(code)
 (P/'Cargo.toml').write_text('[package]\nname="s2k-emit-prefix"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[dependencies]\naspis-statement={path="../native-source/crates/aspis-statement"}\nsolana-program-error="=2.2.2"\n')
 (E/'c3-emit-cuts.json').write_text(json.dumps(cuts,indent=2)+'\n')
 subprocess.run(['rsync','-az',str(P)+'/',HOST+':'+H+'/S2K-emit/'],check=True)
 subprocess.run(['scp',str(E/'c3-emit-cuts.json'),HOST+':'+H+'/'],check=True)
 sys.exit(0)
a=f'extract-{int(sys.argv[2]):03d}';assert phase in ['charon','aeneas'] and not (E/a).exists();name='S2K_EmitSource'
charon='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon';aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
if phase=='charon':
 cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','aspis_core','--opaque','aspis_statement','--opaque','solana_program_error']
 layouts=[]
 for line in (R/'tools/s126-sdk-modular-20261021/extract-owned-host.py').read_text().splitlines():
  if line.startswith('layouts=') or line.startswith('layouts +='): layouts+=ast.literal_eval(line.split('=',1)[1].strip())
 layouts=[p for p in layouts if p.startswith(('aspis_statement::','aspis_core::','solana_program_error::','core::'))]
 layouts+=['aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalResultV1','aspis_statement::pool_v1::historical_anchor::PoolV1TransitionKind']
 for p in layouts: cmd+=['--include',p]
 for f in ['S2K_probe_prefix','S2K_verifier_prefix']:cmd+=['--start-from','crate::'+f]
 cmd+=['--dest-file',H+'/'+name+'.llbc','--','--manifest-path',H+'/S2K-emit/Cargo.toml','--offline','--release','--lib','--jobs','1']
else:cmd=[aeneas,'-log','Translate','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',name,'-dest',H+'/c3-generated','-subdir',name,'-split-files','-emit-json',H+'/'+name+'.llbc']
pins=json.loads(subprocess.check_output(['ssh',HOST,'python3','-'],input=('from pathlib import Path\nimport hashlib,json\npaths='+repr([charon,charon+'-driver',aeneas])+'\nprint(json.dumps({p:dict(sha256=hashlib.sha256(Path(p).read_bytes()).hexdigest(),bytes=Path(p).stat().st_size) for p in paths}))\n').encode()))
deps=dict(native_source_manifest_sha256=sha(E/'native-source.json'),source_cuts_sha256=sha(E/'c3-emit-cuts.json'),tools=pins,scope='Byte-identical source prefixes, terminating immediately before actual syscall; no event, whole-emitter success, or callback correctness is assumed')
if phase=='aeneas':deps['llbc']=json.loads(subprocess.check_output(['ssh',HOST,'python3','-'],input=('from pathlib import Path\nimport hashlib,json\np=Path('+repr(H+'/'+name+'.llbc')+')\nx=json.loads(p.read_text());assert not x["has_errors"]\nprint(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,has_errors=x["has_errors"])))\n').encode()))
x=dict(attempt=a,kind=phase,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=cmd,sources=['S2K-emit/src/lib.rs','S2K-emit/Cargo.toml','c3-emit-cuts.json'],timeout=180,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=H+'/c3-charon-target',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4'),deps_fingerprint=deps,expected_time='optimized compilation then two source prefix translations; no arithmetic elimination')
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n');subprocess.run(['scp',str(E/(a+'.json')),HOST+':'+H+'/'],check=True)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 S2K_reservation.py {a}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2K_run_host.py {a}.json'])
subprocess.run(['scp','-r',HOST+':'+H+'/'+a,str(E/a)],check=True);subprocess.run(['scp',HOST+':'+H+'/'+a+'-reservation.json',str(E)],check=True)
if phase=='aeneas' and r.returncode==0:subprocess.run(['scp','-r',HOST+':'+H+'/c3-generated',str(E/(a+'-generated'))],check=True)
sys.exit(r.returncode)
