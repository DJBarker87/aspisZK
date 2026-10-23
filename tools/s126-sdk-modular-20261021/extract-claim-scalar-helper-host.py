#!/usr/bin/env python3
"""Isolated pure scalar-selector helper candidate; original loops are retained.
Extraction feasibility only: original/source inlining equivalence, concrete
callee and carrier installation remain explicit proof obligations.
"""
from pathlib import Path
import sys,json,hashlib,subprocess,os,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s1-claim-scalar-helper-v1';base=Path('/home/dombarker/project-offloads/s1-current-claim-extraction-v2-20261020/input');phase=sys.argv[1];assert phase in ['charon','aeneas'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if phase=='charon':
 P.mkdir(exist_ok=False);shutil.copytree(base,P/'input')
 src=(base/'lib.rs').read_text();expr='match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()}'
 # Whitespace varies in the retained cut; find exactly its actual statement.
 import re
 match=re.search(r'let scalar\s*=\s*(match point \{0\.\.=2=>sem\.claims\[point\]\[l\],3=>sem\.extra\[l\],4=>sem\.before_z1\[l\],_=>field\(y1,l\)\.c0\(\)\});',src);assert match
 expr=match[1];replacement='let scalar=prepared_claim_scalar(sem,y1,point,l);'
 start=src.index('fn prepared_claim<');assert match.start()>start
 helper='fn prepared_claim_scalar<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],point:usize,l:usize)->K { '+expr+' }\n'
 changed=src[:match.start()]+replacement+src[match.end():];changed=changed[:start]+helper+changed[start:]
 (P/'input/lib.rs').write_text(changed)
 (P/'source-change.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',base_sha256=sha(base/'lib.rs'),candidate_sha256=sha(P/'input/lib.rs'),original_statement=match[0],replacement=replacement,helper=helper,qualification=__doc__),indent=2)+'\n')
 pins=json.loads((base/'source-pins.json').read_text());T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release')
 cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err','--start-from','crate::verifier::prepared_claim',*sum((['--opaque',p] for p in pins['opaque_paths']),[]),'--dest-file',str(P/'ClaimScalar.llbc'),'--','--manifest-path',str(P/'input/Cargo.toml'),'--offline','--release','--lib','--no-default-features','--features','r0,private-leaf-salts','--jobs','1']
else:
 assert not json.loads((P/'ClaimScalar.llbc').read_text())['has_errors']
 A=H/'s1-collapse-tool-recover-v2/source/src/_build/default/main.exe'
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS1NestedClaimScalarHelper','-dest',str(P/'generated'),'-subdir','AspisS1NestedClaimScalarHelper','-split-files','-emit-json',str(P/'ClaimScalar.llbc')]
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(n,None)
tag='s1-claim-scalar-helper-'+phase+'-v1';subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,source_sha256=sha(P/'input/lib.rs'),source_change_sha256=sha(P/'source-change.json'),tool_sha256=sha(Path(cmd[0])),llbc_sha256=sha(P/'ClaimScalar.llbc') if phase=='aeneas' else None,qualification=__doc__,expected_time='Cached optimized compilation/one scalar-selector source cut then nested loop extraction; no arithmetic evaluation or Lean replay.'),indent=2)+'\n');os.chdir(P/'input')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Focused scalar-selector helper candidate; original nested loops and errors retained','--','timeout','180',*cmd]))
