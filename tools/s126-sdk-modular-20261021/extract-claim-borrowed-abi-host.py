#!/usr/bin/env python3
"""Original borrowed claim ABI with private owned scalar arrays and Dot state.
The complete Verified carrier, y1 slice and gamma array retain their original
borrowed caller ABI. No Box clone, allocation or reduced public carrier.
Extraction feasibility only; native equivalence/P6 remain explicit.
"""
from pathlib import Path
import sys,json,hashlib,subprocess,os,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s1-claim-owned-nested-v9';base=Path('/home/dombarker/project-offloads/s1-current-claim-extraction-v2-20261020/input');phase=sys.argv[1];assert phase in ['charon','aeneas'];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if phase=='charon':
 P.mkdir(exist_ok=False);shutil.copytree(base,P/'input')
 src=(base/'lib.rs').read_text()
 start=src.index('fn prepared_claim<');end=src.index(' impl Prepared',start)
 original=src[start:end]
 owned=original.replace('fn prepared_claim<','pub fn prepared_claim_owned<',1)
 owned=owned.replace('sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error>', 'sem:crate::r1_semantic::Verified<H>,y1:[u8;928],inactive:E,g:[E;29],kappa:E)->(Result<E,Error>,crate::r1_semantic::Verified<H>)',1)
 assert owned!=original
 owned=owned.replace('field(y1,l)', 'field(&y1,l)')
 owned=owned.replace('let k=powers::<7>(kappa);','let k=powers::<7>(kappa); let claims=*sem.claims; let extra=sem.extra; let before_z1=sem.before_z1;')
 owned=owned.replace('sem.claims[point][l]','claims[point][l]').replace('sem.extra[l]','extra[l]').replace('sem.before_z1[l]','before_z1[l]')
 statement='dot.push(g[l],scalar).map_err(|_|Error::Parse)?;'
 assert owned.count(statement)==1
 owned=owned.replace(statement,'if dot.push(g[l],scalar).is_err() { return (Err(Error::Parse),sem); }')
 assert owned.count('Ok(claim)')==1
 owned=owned.replace('Ok(claim)','(Ok(claim),sem)')
 helper='fn owned_scalar(claims:[[K;29];3],extra:[K;29],before_z1:[K;29],y1:[u8;928],point:usize,l:usize)->K { match point {0..=2=>claims[point][l],3=>extra[l],4=>before_z1[l],_=>field(&y1,l).c0()} }\n'
 expr='match point {0..=2=>claims[point][l],3=>extra[l],4=>before_z1[l],_=>field(&y1,l).c0()}'
 assert expr in owned
 owned=owned.replace(expr,'owned_scalar(claims,extra,before_z1,y1,point,l)')
 helper+='fn owned_push(mut dot:crate::fast_pairing::EbyKDot,g:[E;29],l:usize,scalar:K)->(Result<(),()>,crate::fast_pairing::EbyKDot) { let r=dot.push(g[l],scalar); (r,dot) }\n'
 owned=owned.replace('if dot.push(g[l],scalar).is_err() { return (Err(Error::Parse),sem); }','let (r,next)=owned_push(dot,g,l,scalar);dot=next;if r.is_err() { return (Err(Error::Parse),sem); }')
 wrapper='pub fn prepared_claim_owned<H:Digest32>(sem:crate::r1_semantic::Verified<H>,y1:[u8;928],inactive:E,g:[E;29],kappa:E)->(Result<E,Error>,crate::r1_semantic::Verified<H>) { let result=owned_claim_loops(*sem.claims,sem.extra,sem.before_z1,y1,inactive,g,kappa); (result,sem) }\n'
 header='pub fn prepared_claim_owned<H:Digest32>(sem:crate::r1_semantic::Verified<H>,y1:[u8;928],inactive:E,g:[E;29],kappa:E)->(Result<E,Error>,crate::r1_semantic::Verified<H>)'
 assert header in owned
 owned=owned.replace(header,'fn owned_claim_loops(claims:[[K;29];3],extra:[K;29],before_z1:[K;29],y1:[u8;928],inactive:E,g:[E;29],kappa:E)->Result<E,Error>')
 owned=owned.replace(' let claims=*sem.claims; let extra=sem.extra; let before_z1=sem.before_z1;','')
 owned=owned.replace('(Err(Error::Parse),sem)','Err(Error::Parse)').replace('(Ok(claim),sem)','Ok(claim)')
 tail_start=owned.index('        let mut claim=E::ZERO;')
 tail_end=owned.index('Ok(claim)',tail_start)+len('Ok(claim)')
 tail=owned[tail_start:tail_end]
 helper+='fn owned_sum(k:&[E;7],parts:&[E;7])->E { '+tail.replace('Ok(claim)','claim')+' }\n'
 owned=owned[:tail_start]+'        Ok(owned_sum(&k,&parts))'+owned[tail_end:]
 helper=helper.replace('y1:[u8;928]','y1:&[u8]').replace('field(&y1,l)','field(y1,l)')
 owned=owned.replace('y1:[u8;928]','y1:&[u8]')
 wrapper='pub fn prepared_claim_owned<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> { owned_claim_loops(*sem.claims,sem.extra,sem.before_z1,y1,inactive,*g,kappa) }\n'
 changed=src[:start]+helper+owned+wrapper+src[start:]
 (P/'input/lib.rs').write_text(changed)
 (P/'source-change.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',base_sha256=sha(base/'lib.rs'),candidate_sha256=sha(P/'input/lib.rs'),original=original,owned=owned,qualification=__doc__,remaining='Source equivalence, exact fixed frame admission, owned return/frame preservation and concrete opaque leaf installation must be proved. This is only extractor feasibility.'),indent=2)+'\n')
 pins=json.loads((base/'source-pins.json').read_text());T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release')
 cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err','--start-from','crate::verifier::prepared_claim_owned',*sum((['--opaque',p] for p in pins['opaque_paths']),[]),'--dest-file',str(P/'ClaimOwned.llbc'),'--','--manifest-path',str(P/'input/Cargo.toml'),'--offline','--release','--lib','--no-default-features','--features','r0,private-leaf-salts','--jobs','1']
else:
 assert not json.loads((P/'ClaimOwned.llbc').read_text())['has_errors']
 A=H/'s1-collapse-tool-recover-v2/source/src/_build/default/main.exe'
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS1OwnedNestedClaim','-dest',str(P/'generated'),'-subdir','AspisS1OwnedNestedClaim','-split-files','-emit-json',str(P/'ClaimOwned.llbc')]
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(n,None)
tag='s1-claim-owned-nested-'+phase+'-v9';subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,source_sha256=sha(P/'input/lib.rs'),source_change_sha256=sha(P/'source-change.json'),tool_sha256=sha(Path(cmd[0])),llbc_sha256=sha(P/'ClaimOwned.llbc') if phase=='aeneas' else None,qualification=__doc__,expected_time='Cached optimized compilation/owned nested source cut, then focused Aeneas extraction; no arithmetic evaluation or Lean replay.'),indent=2)+'\n');os.chdir(P/'input')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Owned complete semantic carrier, original nested loops, returned owner on both paths; feasibility only','--','timeout','180',*cmd]))
