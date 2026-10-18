#!/usr/bin/env python3
"""Prepare test-only no-prover overlay from accepted exact verify injection bytes.
No compiler, Cargo, SBF or runtime job. Production source never written.
"""
import argparse,difflib,hashlib,importlib.util,io,json,re,subprocess,tarfile,tomllib
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];ACCEPTED='6dd9028e9';ARCHIVE='docs/research/100bit-spend-path-20261013/evidence/verify-query-native-20261017/native-evidence.tar.gz';BASE='crates/aspis-r1-cost-probe/';sha=lambda b:hashlib.sha256(b).hexdigest()
def git(ref,path):return subprocess.check_output(['git','-C',str(ROOT),'show',ref+':'+path])
def once(raw,old,new):assert raw.count(old)==1,(old,raw.count(old));return raw.replace(old,new,1)
def build(after,scope="all"):
 after=subprocess.check_output(['git','-C',str(ROOT),'rev-parse',after],text=True).strip();ar=git(ACCEPTED,ARCHIVE);assert sha(ar)=='5c192d1d15fea5207c1f8bb386708b68654ae121dca00eef85792731c2821427';t=tarfile.open(fileobj=io.BytesIO(ar));read=lambda p:t.extractfile('verify-final/source/'+p).read();files={};changes={}
 for p in [BASE+'src/r1_semantic.rs',BASE+'src/lib.rs',BASE+'Cargo.toml']:
  assert git(after,p)==git(ACCEPTED,p),('production source differs',p)
 semantic=read(BASE+'src/r1_semantic.rs');old_guard=b'#[cfg(all(test, feature="prover", feature="private-leaf-salts"))]';assert semantic.count(old_guard)==2
 files[BASE+'src/r1_semantic.rs']=semantic.replace(old_guard,b'#[cfg(all(test, feature="private-leaf-salts"))]')
 h=read(BASE+'src/verify_migration_tests.rs');original_h=h
 h=once(h,b'    for row in out.round_checks { for x in row { k_bytes(x, &mut b); } }\n    k_bytes(out.terminal, &mut b); k_bytes(out.masked_terminal, &mut b);',b'    #[cfg(feature = "prover")]\n    {\n        for row in out.round_checks { for x in row { k_bytes(x, &mut b); } }\n        k_bytes(out.terminal, &mut b); k_bytes(out.masked_terminal, &mut b);\n    }')
 # Reuse the actual fixture public projection, without linking the prover crate.
 helper_path='crates/aspis-prover/src/r0_fixture.rs';helper_source=git(after,helper_path)
 sp=importlib.util.spec_from_file_location('lexer',ROOT/'docs/research/100bit-spend-path-20261013/tools/j1e-source-effect-audit.py');lx=importlib.util.module_from_spec(sp);sp.loader.exec_module(lx);helper=lx.fragment(helper_source,'pub fn statement_public(')[0]
 if isinstance(helper,str):helper=helper.encode()
 assert helper in helper_source
 h=once(h,b'    let public = aspis_prover::r0_fixture::statement_public(&statement);',b'    let public = statement_public(&statement);')
 h=h.replace(b'crate::trace::take()',b'take_values()');assert h.count(b'take_values()')==2
 h=once(h,b'fn run(old: bool, configured: Fault, observed: bool) -> Outcome {',b'use aspis_statement::pool_v1::PoolV1PairForestTerminalStatementV1;\n'+helper+b'\nfn take_values() -> Vec<(u16, usize, [u8; 32])> {\n    #[cfg(feature = "prover")]\n    { crate::trace::take() }\n    #[cfg(not(feature = "prover"))]\n    { Vec::new() }\n}\nfn run(old: bool, configured: Fault, observed: bool) -> Outcome {')
 h=once(h,b'    assert_eq!(&PROOF[..8], b"R1P3COST");',b'    assert!(!cfg!(feature = "prover"), "no-prover gate must not enable prover");\n    assert_eq!(&PROOF[..8], b"R1P3COST");')
 h=once(h,b'            assert_eq!(old, new, "fault={configured:?} observed={observed}");',b'            assert_eq!(old, new, "fault={configured:?} observed={observed}");\n            assert!(old.values.is_empty() && new.values.is_empty(), "production no-prover trace values are disabled");')
 files[BASE+'src/verify_migration_tests.rs']=h
 lib=git(after,BASE+'src/lib.rs');files[BASE+'src/lib.rs']=once(lib,b'#[cfg(feature = "prover")]\nextern crate std;',b'#[cfg(any(test, feature = "prover"))]\nextern crate std;')
 manifest=git(after,BASE+'Cargo.toml');assert b'[dev-dependencies]' not in manifest;files[BASE+'Cargo.toml']=manifest+b'\n# Test-only SHA for the saved no-prover injection gate.\n[dev-dependencies]\nsha2 = { workspace = true }\nserde_json.workspace = true\n'
 originals={BASE+'src/r1_semantic.rs':semantic,BASE+'src/verify_migration_tests.rs':original_h,BASE+'src/lib.rs':lib,BASE+'Cargo.toml':manifest}
 # Query102 retains exact old/new bodies; adapt only test selection and snapshots.
 transcript= t.extractfile('query/source/'+BASE+'src/transcript.rs').read()
 assert git(after,BASE+'src/transcript.rs')==git(ACCEPTED,BASE+'src/transcript.rs')
 qguard=b'all(test,feature="prover",feature="private-leaf-salts")';assert transcript.count(qguard)==4
 files[BASE+'src/transcript.rs']=transcript.replace(qguard,b'all(test,feature="private-leaf-salts")')
 q=t.extractfile('query/source/'+BASE+'src/query_migration_tests.rs').read();original_q=q
 q=q.replace(b'crate::trace::take()',b'take_values()');assert q.count(b'take_values()')==2
 q=once(q,b'#[test]\nfn queries_exact_old_new_all_digest_positions_and_decoder() {',b'fn take_values()->Vec<(u16,usize,[u8;32])>{\n #[cfg(feature="prover")] {crate::trace::take()}\n #[cfg(not(feature="prover"))] {Vec::new()}\n}\n#[test]\nfn queries_exact_old_new_all_digest_positions_and_decoder() {\n assert!(!cfg!(feature="prover"),"no-prover query gate");')
 q=once(q,b'assert_eq!(b.trace.len(),22);for i in 0..22 {assert_eq!(b.trace[i],(5,i,E::from_m31(aspis_core::field::M31(q[i])).to_le_bytes()));}',b'assert!(b.trace.is_empty(),"production no-prover trace values are disabled");')
 q=once(q,b'assert_eq!(a,b,"{} {:?}",label,fault);',b'assert_eq!(a,b,"{} {:?}",label,fault);assert!(a.trace.is_empty()&&b.trace.is_empty());')
 q=q.replace(b'trace_indices=0..21',b'trace_values=disabled-no-prover returned_query_indices=0..21')
 files[BASE+'src/query_migration_tests.rs']=q
 context_path=BASE+'src/query_migration_context.json';context=t.extractfile('query/source/'+context_path).read();files[context_path]=context
 originals.update({BASE+'src/transcript.rs':transcript,BASE+'src/query_migration_tests.rs':original_q,context_path:context})
 # Saved proof counter needs only two actual prover helper declarations.
 counter_path='tools/r1-hash-input-counter/';counter=git(after,counter_path+'src/main.rs');hash_src=git(after,'crates/aspis-prover/src/lib.rs');hash_helper=lx.fragment(hash_src,'pub fn host_hashv(')[0].encode();assert hash_helper in hash_src
 counter_new=once(counter,b'aspis_prover::host_hashv(parts)',b'host_hashv(parts)');counter_new=once(counter_new,b'aspis_prover::r0_fixture::statement_public(&statement)',b'statement_public(&statement)')
 counter_new+=b'\nuse aspis_statement::pool_v1::{PoolV1PairForestTerminalStatementV1, pair_forest_semantic_terminal::r0::Public};\n'+helper+b'\n'+hash_helper+b'\n'
 cp=git(after,counter_path+'Cargo.toml');cp_new=once(cp,b'aspis-prover = { path = "../../crates/aspis-prover", features = ["r0", "insecure-spend-fixture"] }\n',b'');cp_new=once(cp_new,b'features = ["prover", "private-leaf-salts"]',b'features = ["private-leaf-salts"]')
 lock=git(after,counter_path+'Cargo.lock');start=lock.index(b'name = "r1-hash-input-counter"');end=lock.index(b'\n[[package]]',start);part=lock[start:end];part_new=once(part,b' "aspis-prover",\n',b'');lock_new=json.loads((HERE/'counter-lock-refresh.json').read_text())['text'].encode();bd={(p['name'],p['version'],p.get('source')):p for p in tomllib.loads(lock.decode())['package']};ad={(p['name'],p['version'],p.get('source')):p for p in tomllib.loads(lock_new.decode())['package']};assert all(k in bd and p.get('checksum')==bd[k].get('checksum') for k,p in ad.items());assert {k[0] for k in bd if k not in ad}=={'aspis-prover','getrandom','r-efi','wasip2','wit-bindgen','zeroize'}
 for path,old,new in [(counter_path+'src/main.rs',counter,counter_new),(counter_path+'Cargo.toml',cp,cp_new),(counter_path+'Cargo.lock',lock,lock_new)]:originals[path]=old;files[path]=new
 for p,b in files.items():changes[p]={'before_sha256':sha(originals[p]),'after_sha256':sha(b),'unified_diff':''.join(difflib.unified_diff(originals[p].decode().splitlines(True),b.decode().splitlines(True),fromfile='accepted-test-overlay/'+p,tofile='no-prover-test-overlay/'+p))}
 plan={'classification':'TEST_ONLY_NO_PROVER_VERIFY_QUERY_COUNTER_OVERLAY_NOT_RUN','after_revision':after,'accepted_archive':{'git_revision':subprocess.check_output(['git','-C',str(ROOT),'rev-parse',ACCEPTED],text=True).strip(),'git_path':ARCHIVE,'sha256':sha(ar)},'production_files_match_accepted_6dd':True,'production_candidate_modified':False,'old_new_verify_instrumentation':'Exact previously accepted wrapper bodies; only module/old-body test guards remove prover. Existing production cfg(not(prover)) branches now compile.','hash_helper_copy':{'source_path':'crates/aspis-prover/src/lib.rs','source_sha256':sha(hash_src),'declaration_sha256':sha(hash_helper),'transformation':'byte-exact host_hashv declaration/body copied into counter only; no prover dependency.'},'helper_copy':{'source_path':helper_path,'source_revision':after,'source_sha256':sha(helper_source),'declaration_sha256':sha(helper),'transformation':'byte-exact helper declaration/body, actual statement type imported; only harness call target is local. No aspis_prover dependency.'},'changes':changes,'overlay_files':{p:sha(b) for p,b in files.items()},'generator_sha256':sha(Path(__file__).read_bytes()),'coverage':{'faults':55,'success_controls':1,'observer_modes':['None','Some'],'cases_per_feature_build':112,'feature_builds':{'default':'private-leaf-salts,optimized-terminal','detail':'private-leaf-salts,optimized-terminal,detail-phases'},'prover':False,'all_errors_events_digests_phases_equal':True,'all_deployed_shape_returned_fields_equal':True,'native_trace_values':'Actual production no-prover value recording remains disabled; both snapshots asserted empty.'},'fixture_files':{f:sha(read(f)) for f in ['docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-proof.bin','docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-public-asf8.bin']},'admission_policy':{'override':'User: just do it in parallel (root clarified A/B may overlap when aggregate fits).','B_phase_lock':'/tmp/aspis-r1-worker-b-native.lock','foreign_activity':'record only, never signal or stop based solely on foreign arrival','own_limits':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0},'aggregate_MemoryMax_maximum_GiB':55,'continuous_admission_check':True},'gates':[],'new_builds':0}
 for name,features in plan['coverage']['feature_builds'].items():
  plan['gates'].append({'label':'verify-no-prover-'+name,'command':['/home/dombarker/.cargo/bin/cargo','test','--verbose','--release','--locked','--offline','-j1','-p','aspis-r1-cost-probe','--features',features,'--lib','r1_semantic::verify_migration_tests::verify_saved_s2_exact_old_new_all_round_failures_and_success','--','--nocapture','--test-threads=1'],'required_rustc_cost_probe_features':sorted(['default']+features.split(',')),'required_absent_extern':'aspis_prover','scope_limits':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0},'required_case_lines':112,'required_test_result':'1 passed; 0 failed','production_reachability':'Actual saved S2; symmetric injected wrapper failures remain test-only.'})
 plan['gates'].append({'label':'query-no-prover-102','command':['/home/dombarker/.cargo/bin/cargo','test','--verbose','--release','--locked','--offline','-j1','-p','aspis-r1-cost-probe','--features','private-leaf-salts,optimized-terminal','--lib','transcript::query_migration_tests::queries_exact_old_new_all_digest_positions_and_decoder','--','--nocapture','--test-threads=1'],'required_rustc_cost_probe_features':['default','optimized-terminal','private-leaf-salts'],'required_absent_extern':'aspis_prover','required_case_lines':102,'required_test_result':'1 passed; 0 failed','scope_limits':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0}})
 plan['gates'].append({'label':'counter-no-prover-583','command':['/home/dombarker/.cargo/bin/cargo','run','--verbose','--release','--locked','--offline','-j1','--manifest-path','tools/r1-hash-input-counter/Cargo.toml','--','{root}/fixtures/r1-s2-proof.bin','{root}/fixtures/r1-s2-public-asf8.bin','{root}/ordered-counter-no-prover.json',after],'required_rustc_cost_probe_features':['default','private-leaf-salts'],'required_absent_extern':'aspis_prover','ordered_calls':583,'tx1_calls':349,'tx2_calls':234,'scope_limits':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0}})
 if scope=='counter':
  allowed={counter_path+'src/main.rs',counter_path+'Cargo.toml',counter_path+'Cargo.lock'};files={p:b for p,b in files.items() if p in allowed};plan['overlay_files']={p:h for p,h in plan['overlay_files'].items() if p in allowed};plan['changes']={p:d for p,d in plan['changes'].items() if p in allowed};plan['gates']=[g for g in plan['gates'] if g['label']=='counter-no-prover-583'];plan['classification']='CLEAN_PRODUCTION_NO_PROVER_COUNTER_TOOL_OVERLAY_NOT_RUN';plan['coverage']={'ordered_calls':583,'tx1_calls':349,'tx2_calls':234,'production_source':'CLEAN Git234; no injection wrappers/test-only modules/devdeps in verifier crate','prover':False};plan['old_new_verify_instrumentation']='NOT_APPLIED: counter-only clean source';plan['source_scope']='counter'
 else:plan['source_scope']='all'
 return files,plan

def main():
 a=argparse.ArgumentParser();a.add_argument('--after',required=True);a.add_argument('--scope',choices=['all','counter'],default='all');a.add_argument('--stage',type=Path);a.add_argument('--check',action='store_true');args=a.parse_args();files,plan=build(args.after,args.scope);out=(json.dumps(plan,indent=2,sort_keys=True)+'\n').encode();path=HERE/'source-pins.json'
 if args.check:assert path.read_bytes()==out
 else:path.write_bytes(out)
 if args.stage:
  for name,b in files.items():
   dest=args.stage/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 print(json.dumps({'status':'PASS_PREPARE_NO_COMPILER','after':plan['after_revision'],'source_pins_sha256':sha(out),'overlay_files':len(files),'native_jobs':0}))
if __name__=='__main__':main()
