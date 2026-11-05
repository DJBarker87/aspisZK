"""Per-deployed-label actual error/String/syscall/cleanup composition, no DebugLog credit."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry4-20261106';R=E.parents[1]
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text())
def source(root,a,rel):
 p=root/a/'sources'/rel
 if p.exists():return p.read_text()
 idx=read(root/('NIJ_INPUTS.json' if root==E else 'NHY_INPUTS.json'));h=idx['attempts'][a][rel];b=lzma.decompress((root/idx['objects'][h]['path']).read_bytes());assert sha(b)==h;return b.decode()
def log(root,a):return lzma.decompress((root/a/'stdout.log.xz').read_bytes()).decode()
def passing(root,a,negative=False):
 r=read(root/a/'receipt.json');s=log(root,a)
 assert r['exit_status']==(1 if negative else 0) and 'timed out' not in s
 if negative:assert re.search(r'\*\* 1 of \d+ failed',s) and 'Failed Checks:' in s and 'unwinding assertion' not in s
 else:assert 'VERIFICATION:- SUCCESSFUL' in s
 assert read(root/(a+'-graph-check.json'))['graph_matches_frozen'];assert read(root/(a+'-erasure-check.json'))['passed'];assert read(root/(a+'-lock-check.json'))['unchanged']
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 return r
labels=['Parse','Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation'];pairs=[(70,71)]+[(k,k+1) for k in range(73,86,2)];rows=[]
for index,(label,(pos,neg)) in enumerate(zip(labels,pairs)):
 pa,na=f'NIJ_K{pos:03}',f'NIJ_K{neg:03}';pr,nr=passing(E,pa),passing(E,na,True)
 for r in [pr,nr]:
  cmd=r['native_command'];assert cmd[cmd.index('--features')+1]=='pool-adapter,private-leaf-salts'
  closure=read(E/(r['attempt']+'-graph-check.json'))['selected_closure'];features=next(p['features'] for p in closure if p['name']=='aspis-r1-cost-probe');assert 'prover' not in features and 'cu-profiling' not in features
 s=source(E,pa,'NIJ_src/programs/r1-cost-probe/src/NIJ_error.rs')
 head=s[s.index('fn log_error_'+label.lower()+'('):s.index('fn error_'+label.lower()+'()')]
 assert 'message=="r1:error:'+label+'"' in head
 assert '#[kani::stub(core::fmt::Arguments::as_str,arguments_as_str)]' in head
 assert '::Write>::write_str,writer_' not in head,'Actual String writer must execute'
 body=s[s.index('fn error_'+label.lower()+'()'):];body=body[:body.index('\n}')+2]
 assert 'super::error(verifier::Error::'+label+')' in body and 'ProgramError::InvalidInstructionData' in body
 assert 'ManuallyDrop' not in body and 'forget' not in body and 'static ' not in body
 cap=36 if len('r1:error:'+label)>18 else 18
 cp,cn=f'NIJ_K{87+2*index:03}',f'NIJ_K{88+2*index:03}';passing(E,cp);passing(E,cn,True)
 cs=source(E,cp,'NIJ_src/programs/r1-cost-probe/src/NIJ_error.rs');cb=cs[cs.index('unsafe fn free_cleanup_'+label.lower()+'('):];cb=cb[:cb.index('\n}')+2]
 assert 'layout.align()==1' in cb and 'layout.size()==18||layout.size()==36' in cb and f'layout.size()=={cap}' in cb
 assert 'bytes==b"r1:error:'+label+'"' in cb
 rows.append(dict(label=label,message='r1:error:'+label,positive=pa,negative=na,cleanup_positive=cp,cleanup_negative=cn,initial_capacity=18,final_capacity=cap,bytes=len('r1:error:'+label)))
# Same-name/constant family stability; no verdict changed by renaming.
passing(E,'NIJ_K072');passing(E,'NIJ_K109',True)
# NoShortcut is a CLOSED compiler-metadata value cut on exactly this literal/all Error values.
passing(P,'NHY_K111');passing(P,'NHY_K112',True)
ms=source(P,'NHY_K111','NHY_src/programs/r1-cost-probe/src/NHY_error.rs');assert 'fn format_capacity_packet(e:verifier::Error)->bool' in ms
assert 'format_args!("r1:error:{:?}",e).estimated_capacity()==18' in ms and 'format_args!("r1:error:{:?}",e).as_str().is_none()' in ms
assert 'kani::assume(tag<8)' in ms
for label in labels:assert 'verifier::Error::'+label in ms
src=subprocess.check_output(['git','show',F+':programs/r1-cost-probe/src/lib.rs'],cwd=R,text=True)
assert 'fn error(e:verifier::Error)->ProgramError{msg!("r1:error:{:?}",e);ProgramError::InvalidInstructionData}' in src
# Pure String dispatch/value packets plus actual returning root and actual Drop
# are independent of the quarantined DebugLog receiver calibration.
for pos,neg in [(5,6)]+[(k,k+1) for k in range(8,21,2)]+[(k,k+1) for k in range(23,38,2)]+[(k,k+1) for k in range(40,55,2)]:passing(E,f'NIJ_K{pos:03}');passing(E,f'NIJ_K{neg:03}',True)
raw=read(E/'NIJ_stage2_audit/proof1.json');assert raw['exit_status']==0
for name in ['NIJ_ErrorJoin.source','NIJ_ErrorJoin.bytes','NIJ_ErrorJoin.exhaustive','NIJ_ErrorJoin.abort_prefix','NIJ_ArgumentMetadata.as_str_none','NIJ_ArgumentMetadata.choose','NIJ_StringCleanup.account_frame','NIJ_StringCleanup.growth_frame','AspisR1.RPx_Deployed.deployed']:
 r=next(r for r in raw['results'] if r['root']==name);assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}
scan=read(E/'NIJ_stage2_audit/scan_summary.json');assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
out=dict(status='PASS_ERROR_NATIVE_MODEL_ASSOCIATION',rows=['TX1:NGB001','TX2:211'],frozen_revision=F,frozen_source_sha256=sha(src.encode()),instantiations=rows,route='y/al: actual frozen root, actual String writer/format/growth/drop, calibrated compiler NoShortcut boundary, syscall argument and cleanup packets',metadata_cut=dict(native=['NHY_K111','NHY_K112'],stub='arguments_as_str',reference='NIJ_ArgumentMetadata.image',theorems=['capacity','as_str_none','choose'],domain='ONLY format_args!(r1:error:{:?},e), every deployed Error constructor, features exclude prover. Real native value is18/None; it is not a law for arbitrary Arguments. Explicit Std None constructor reference, no extraction or generic std-source identity claimed.',wrong_stub_control='NIJ_K109: Some(corrupted) makes the actual root fail at the real logging argument'),writer='Every full root uses actual String Write body; no writer substitution. Separate writer/dispatch/append native packets are support, not the sole root certificate. DebugLog is never selected.',runtime='Exact bytes reach solana_program::log::sol_log; unit reply unchanged. Runtime logging/allocator return and abort-prefix semantics stay existing P6/std/runtime trust, no syscall value modeled. One msg call in exact frozen source; controls prove syscall/cleanup reachability.',cleanup='Actual String Drop executes in the returning roots. Separate per-label dealloc argument packets retain old-cap18/new-cap36 pointers/layout/read-only live contents; deallocation effect uses existing allocator primitive, NIJ_StringCleanup account/growth frames on fresh private allocations. No account or key argument, no writable static, no new runtime assumption.',model='NIJ_ErrorJoin.source/exhaustive/bytes: full Result/state/error port, exact eight-label UTF8 table. Abort prefixes retain fail/div with no suffix; no successful formatting/logging or final-output premise.',trust='P6/D188 option-A native semantic transport retained/reclassified; accepted Std/allocator/compiler/runtime realization retained. No new assumption or RuntimeCpiReadonlyEntry7.',whole_entry_path=False)
(E/'NIJ_ERROR_ASSOCIATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(status=out['status'],rows=out['rows'])))
