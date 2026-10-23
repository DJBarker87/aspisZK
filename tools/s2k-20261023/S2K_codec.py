from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2k-20261023';T=Path(__file__).parent
HOST='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-cx-s2k-20261023'
sha=lambda b:hashlib.sha256(b).hexdigest()
def fun(path,anchor):
 s=(R/path).read_text();a=s.index(anchor);b=s.index('{',a);depth=1;i=b+1
 while depth: depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
if sys.argv[1]=='prepare':
 p=E/'S2K-codec';p.mkdir(exist_ok=True)
 base=(D/'tools/terminal-result-constructor-extraction-kit/lib.rs').read_text()
 # Retained pure declarations and constructor; append only actual source methods.
 word=fun('crates/aspis-core/src/field.rs','pub fn to_le_bytes(self) -> [u8; 4]')
 digest=fun('crates/aspis-statement/src/atomic_statement.rs','pub fn encode_digest_canonical(')
 f='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';s=(R/f).read_text();start=s.index('    let mut output = [0u8; POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES];',s.index('pub fn encode_pool_v1_pair_forest_terminal_result_v1('));end=s.index('    Ok(output)',start);body=s[start:end]
 old='''    output[RESULT_AFTERSTATE_OFFSET..].copy_from_slice(
        &encode_pool_v1_pair_verified_afterstate_v1(&result.verified_afterstate)
            .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Afterstate(error))?,
    );''';assert old in body
 body=body.replace(old,'    output[RESULT_AFTERSTATE_OFFSET..].copy_from_slice(afterstate);')
 constants=[]
 for name in ['POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC','POOL_V1_PAIR_FOREST_TERMINAL_VERSION','POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES','RESULT_MASTER_OFFSET','RESULT_SELECTED_LANE_OFFSET','RESULT_NULLIFIER_OFFSET','RESULT_AFTERSTATE_OFFSET']:
  import re
  m=re.search(r'(?:pub )?const '+name+r'\b[\s\S]*?=[\s\S]*?;',s);assert m,name;constants.append(m.group())
 # The result-width expression depends on the source afterstate width688.
 constants+=['const POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES: usize = 688;','const POOL_V1_DIGEST_ENCODING_VERSION: u8 = 1;']
 lib=base+'\nimpl M31 {\n'+word+'\n}\n'+digest+'\n'+'\n'.join(constants)+'\n\npub fn encode_fields(result: &PoolV1PairForestTerminalResultV1, afterstate: &[u8;688]) -> [u8;792] {\n'+body+'    output\n}\n'
 (p/'lib.rs').write_text(lib);(p/'Cargo.toml').write_text('[package]\nname="s2k-result-codec"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[lib]\npath="lib.rs"\n')
 (E/'codec-source.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source=f,source_sha256=sha(s.encode()),original_field_body=s[start:end],cut_body=body,word=word,digest=digest,lib_sha256=sha(lib.encode()),adaptations=['Reuse source-pinned constructor declarations unchanged.','Source field encoding cut begins after validate_result success.','The afterstate child result is an explicit688-byte parameter, substituted only at its already-checked copy boundary (Kani045).','Source constants retain values;688 and digest version1 match the pinned source.','No validation, SDK, allocator, syscall or successful-emitter premise is represented.']),indent=2)+'\n')
 subprocess.run(['rsync','-az',str(p)+'/',HOST+':'+H+'/S2K-codec/'],check=True)
 sys.exit(0)
phase=sys.argv[1];assert phase in ['charon','aeneas'];a=f'extract-{int(sys.argv[2]):03d}';assert not (E/a).exists()
charon='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
aeneas='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
llbc_pin=None
if phase=='aeneas':
 script='from pathlib import Path\nimport hashlib,json\np=Path('+repr(H+'/S2K_ResultCodec.llbc')+')\nx=json.loads(p.read_text())\nassert not x["has_errors"]\nprint(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,has_errors=x["has_errors"])))\n'
 llbc_pin=json.loads(subprocess.check_output(['ssh',HOST,'python3','-'],input=script.encode()))
 (E/(a+'-llbc-pin.json')).write_text(json.dumps(llbc_pin,indent=2)+'\n')
cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from',('crate::'+sys.argv[3] if len(sys.argv)>3 else 'crate::encode_fields'),'--dest-file',H+'/S2K_ResultCodec.llbc','--','--manifest-path',H+'/S2K-codec/Cargo.toml','--offline','--release','--lib','--jobs','1'] if phase=='charon' else [aeneas,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',(sys.argv[3] if len(sys.argv)>3 else 'S2K_ResultCodec'),'-dest',H+'/codec-generated','-subdir',(sys.argv[3] if len(sys.argv)>3 else 'S2K_ResultCodec'),'-split-files','-emit-json',H+'/S2K_ResultCodec.llbc']
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',CARGO_TARGET_DIR=H+'/codec-charon-target',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
pins=json.loads(subprocess.check_output(['ssh',HOST,'python3','-'],input=('from pathlib import Path\nimport hashlib,json\npaths='+repr([charon,charon+'-driver',aeneas])+'\nprint(json.dumps({p:dict(sha256=hashlib.sha256(Path(p).read_bytes()).hexdigest(),bytes=Path(p).stat().st_size) for p in paths}))\n').encode()))
(E/(a+'-tool-pins.json')).write_text(json.dumps(pins,indent=2)+'\n')
x=dict(attempt=a,kind=phase,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=cmd,sources=['S2K-codec/lib.rs','S2K-codec/Cargo.toml'],timeout=180,env=env,deps_fingerprint={'codec_manifest_sha256':sha((E/'codec-source.json').read_bytes()),'current_lib_sha256':sha((E/'S2K-codec/lib.rs').read_bytes()),'suffix_cut_sha256':sha((E/'codec-suffix-source.json').read_bytes()) if (E/'codec-suffix-source.json').exists() else None,'tools':pins,'llbc_input':llbc_pin,'scope':'source field cut only; no opaque validation/syscall callback'},expected_time='optimized MIR extraction/translation of one small source codec; no arithmetic execution')
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
subprocess.run(['scp',str(E/(a+'.json')),str(T/'S2K_run_host.py'),HOST+':'+H+'/'],check=True)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 S2K_reservation.py {a}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2K_run_host.py {a}.json'])
subprocess.run(['scp','-r',HOST+':'+H+'/'+a,str(E/a)],check=True);subprocess.run(['scp',HOST+':'+H+'/'+a+'-reservation.json',str(E)],check=True)
if phase=='aeneas' and r.returncode==0:subprocess.run(['scp','-r',HOST+':'+H+'/codec-generated',str(E/(a+'-generated'))],check=True)
sys.exit(r.returncode)
