"""Frozen snapshot read footprint and named stage-cut association, no build."""
from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def body(text,name):
 i=text.index('fn '+name+'(');i=text.index('{',i);j=i+1;d=1
 while d:d+=(text[j]=='{')-(text[j]=='}');j+=1
 return text[i+1:j-1]
norm=lambda s:re.sub(r'\s+','',s)
raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'])
f=raw.decode();snapshot=body(f,'snapshot');native=(E/'NHY_snapshot.rs.txt').read_text();b=norm(body(native,'header_clone_cut'))
assert 'matchaccount.try_borrow_data()' in norm(snapshot)
assert 'letlength=data.len();' in norm(snapshot)
assert 'iflength==length1||length==length2{Ok(data.to_vec())}else{Err(ProgramError::InvalidAccountData)}' in norm(snapshot)
assert 'Err(error)=>(Err(error.clone()),Err(error))' in norm(snapshot)
expected=norm('''let (length,bytes)=match borrowed_oracle(a,bytes,log){
 Ok(data)=>{let length=data.len();if length==l1||length==l2{return Head::Copy{length};}(Ok(length),Err(ProgramError::InvalidAccountData))}
 Err(error)=>{clone.expected=&error;let result=clone_oracle(&error,clone);(Err(result),Err(error))},
 };OwnedAccount{key:*a.key,owner:*a.owner,is_signer:a.is_signer,is_writable:a.is_writable,executable:a.executable,length,bytes}''')
expected=expected.replace('};OwnedAccount{','};Head::Done(OwnedAccount{')[:-1]+'})'
assert b==expected
# Exact field list is unchanged; only SDK/clone calls and before-copy continuation split.
assert 'if log.ok{Ok(bytes)}else{Err(ProgramError::AccountBorrowFailed)}' in native
assert 'l.receiver=e;l.reply=kani::any();if l.reply{ProgramError::AccountBorrowFailed}else{ProgramError::InvalidAccountData}' in native
assert 'if ok{if length==l1||length==l2{0}else{1}}else{2}' in native
assert not re.search(r'\bstatic\s+(mut\b|[A-Za-z_]\w*\s*:)',native)
assert 'copy_oracle' not in native
out=dict(status='PASS',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_file_sha256=sha(raw),frozen_snapshot_sha256=sha(snapshot.encode()),native_sha256=sha(native.encode()),root='SAME S2W_D189Entry.Entry.heap, counter is computed zero; NHY_SnapshotRoot.returning derives guard acquisition and restored heap using accepted SDK15, relatedness and validity only',both_arms='Borrowed-slice Result explicit Ok(original slice)/Err(AccountBorrowFailed), local receiver/pointer/length/reply log; cloned error arbitrary two-constructor reply with NGL/NHD exact canonical clone law',length_domain='All usize descriptor dispatch K008/K009 plus exact emitted header/finish chain and NHJ all-usize K078/K079. Physical one-byte log calibration K005/K006 reads only source descriptor; it is not a whole-buffer test or an inferred runtime upper bound.',copy='No custom copy stub. Retained actual allocation + exact KMX single-byte value/frame + Lean initialized-copy induction + set_len + nine capacity return frames; NHJ actual caller size table proves allocating domains1..58295.',cleanup='Input AccountInfo and returned OwnedAccount are borrowed/returned by snapshot, not destroyed there. Their harness ownership uses ManuallyDrop. Actual callee-owned shared guard bracket/deref/drop is separately NHJ_K075..077 + SDK15 + NHY root theorem. Allocator abort/div retained.',scope='P6/D188 option-A source/native semantic transport retained reclassification; no new trust row, no RuntimeCpiReadonlyEntry7, no success or output premise')
(E/'NHY_SOURCE_ASSOCIATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
