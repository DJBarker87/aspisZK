"""Strict source-footprint checks for composed snapshot and route packets."""
from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def frozen(n):return subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
def norm(s):return re.sub(r'\s+','',s)
def body(s,name):
 i=s.index('fn '+name+'(');i=s.index('{',i);depth=1;j=i+1
 while depth:depth+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i+1:j-1]
owned=frozen('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs');route=frozen('programs/r1-cost-probe/src/pool_route.rs');native=(E/'NHJ_owned.rs.txt').read_text()
assert norm(body(route,'admitted'))=='data==[3,10]||data==[3,11]||data.starts_with(b"ASQ8")'
assert norm(body(native,'snapshot_selected'))=='length==length1||length==length2'
snapshot=norm(body(owned,'snapshot'));assert 'letlength=data.len();' in snapshot and 'iflength==length1||length==length2{Ok(data.to_vec())}else{Err(ProgramError::InvalidAccountData)}' in snapshot
assert 'Err(error)=>(Err(error.clone()),Err(error))' in snapshot and 'forget' not in snapshot
assert norm(body(native,'rejected_construct'))=='OwnedAccount{key:*k,owner:*o,is_signer:s,is_writable:w,executable:e,length:Ok(length),bytes:Err(ProgramError::InvalidAccountData)}'
assert 'copy_oracle' not in native
std=(E/'NHJ_rust_slice.rs.txt').read_text();assert 'let mut v = Vec::with_capacity_in(s.len(), alloc);' in std and 's.as_ptr().copy_to_nonoverlapping(v.as_mut_ptr(), s.len());' in std and 'v.set_len(s.len());' in std
core=(E/'NHJ_rust_slice_mod.rs.txt').read_text();assert norm(body(core,'starts_with'))=='letn=needle.len();self.len()>=n&&needle==&self[..n]'
cmp=(E/'NHJ_rust_slice_cmp.rs.txt').read_text();special=cmp[cmp.index('impl<A, B> const SlicePartialEq<B>'):];assert 'if self.len() != other.len()' in special and 'compare_bytes(self.as_ptr() as *const u8, other.as_ptr() as *const u8, size) == 0' in special
assert 'match self.as_array::<N>()' in (E/'NHJ_rust_array_equality.rs.txt').read_text()
assert 'if self.len() == N' in core and 'self.as_ptr().cast_array()' in core
assert 'crate::intrinsics::raw_eq(a, crate::mem::transmute(b))' in (E/'NHJ_rust_array_equality.rs.txt').read_text()
assert 'get_offset_len_noubcheck' in (E/'NHJ_rust_slice_index.rs.txt').read_text()
for name,pin in [('NHJ_rust_slice.rs.txt','NHJ_STD_SLICE_PIN.json'),('NHJ_rust_slice_mod.rs.txt','NHJ_rust_slice_mod.rs.pin.json'),('NHJ_rust_slice_cmp.rs.txt','NHJ_rust_slice_cmp.rs.pin.json'),('NHJ_rust_slice_index.rs.txt','NHJ_rust_slice_index.rs.pin.json'),('NHJ_rust_array_equality.rs.txt','NHJ_RUST_ARRAY_EQUALITY_PIN.json')]:
 assert sha((E/name).read_bytes())==json.loads((E/pin).read_text())['sha256']
reuse=json.loads((E/'NHJ_ROUTE_REUSE.json').read_text());assert reuse['rust_input_revalidated'] and sha((E/'NHJ_route_ref_input.rs.txt').read_bytes())==reuse['exact_rust_reference_sha256']
assert reuse['generating_receipt']['exit_status']==0 and 'crate::admitted_ref' in reuse['generating_pins']['charon_command']
line=next(l for l in (E/'NHJ_route_ref_input.rs.txt').read_text().splitlines()if l.startswith('pub fn admitted_ref'));assert line in native
# Finalize's cap precondition is established by the strengthened exact-capacity gate.
assert 'v.len()==0&&v.capacity()==n' in body(native,'allocation_exact_packet')
assert 'bytes.truncate(count);' in body(native,'sdk_summary_family')
assert 'copy_unit_frame(src,output)' in body(native,'sdk_summary_family')
assert 'Vec::<u8>::with_capacity(count)' in body(native,'sdk_summary_family') and 'dst.spare_capacity_mut()[index]' in body(native,'sdk_summary_family')
assert 'assert_eq!(src as *const u8,source.wrapping_add(index))' in body(native,'sdk_summary_family')
assert 'assert_eq!(output.as_mut_ptr(),destination.wrapping_add(index))' in body(native,'sdk_summary_family')
assert 'sourceByte' not in body(native,'sdk_summary_family')
x=dict(status='PASS',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_sha256=sha(Path(__file__).read_bytes()),snapshot=dict(scope='SOURCE_AND_LOCAL_SUPPORT_ONLY; TX1:343/TX2:239 OPEN: actual deployed Entry.snapshot borrow-error join missing',source_sha256=sha(owned.encode()),cases=['SDK borrow error ABF: exact error move/clone; NGL/NHD canonical real-body/frames reused','Borrow success, nonmatching length: no allocation, generic all-usize selector and complete rejected constructor K078..081','Borrow success, admitted positive size: exact-capacity allocation K065/066 -> KMX byte step K039/040 and retained loop/frame laws -> actual set_len K041/042 -> after-copy continuation K015..032','All valid SDK counts/fresh affine names: NHJ_SdkDomains and NHJ_SnapshotPacket.bracket_all','SDK context through actual allocation/copy frame: K075/076/077; Unit/reference shape K067..071; strong copied value comes only from K039/040 plus KMX induction'],caller_domains='Actual firstSizes/secondSizes, NHJ_EntryDomains and NHJ_SnapshotPacket.caller_domains; nonempty1..58295 only on allocating branch; malformed actual lengths unrestricted on rejection',abort='Private allocator failure is abort/divergence, not an inner ProgramError; existing P2-P4/D189 Allocator interface retains that partial terminal. No caller success/acceptance premise.',trust='Existing SDK15, std/allocator/cleanup, compiler/ABI/source-to-ELF and P6/D188 option-A semantic transport explicitly used as reclassification. No new assumption.'),route=dict(source_sha256=sha(route.encode()),read_footprint=['Slice/array equality uses as_array<N>, which checks self.len()==N before constructing a borrowed array at the same pointer; None returns false. N=2; scalar/metadata constructor classification from exact pinned array/slice source.','len=2 uses exact2-byte original window; K084/085','len>=4 uses checked scalar guard then borrowed prefix of length4; std starts_with exact source above. Prefix construction is a scalar pointer/length operation with start0/end4<=len; no whole buffer or new output bytes are assumed. K082/083 verifies all descriptor words/four bytes.','Remaining lengths are exactly0,1,3 and return false without payload comparison; physical K086/087.','Array BytewiseEq uses raw_eq on exactly2-byte arrays after as_array<2> succeeds; Slice BytewiseEq compares size_of_val only after equal-length guard, and starts_with compares needle length4 with source prefix length4. Physical2-byte,4-byte and zero/one/three-byte gates close each read window; no four-byte reference is imposed on a two-byte caller. Typed admission proves borrowed ranges, retained compiler/ABI/std and RuntimeMemcmp realization remain explicit.'],full_model=['NHJ_RoutePacket.extracted','NHJ_RoutePacket.associate','NHJ_RouteFrame.four_window','NHJ_RouteFrame.rejected_short'],no_upper_instruction_length_bound=True,no_fake_large_slice=True,no_new_runtime_assumption=True),quarantine=json.loads((E/'NHJ_QUARANTINE.json').read_text())['attempts'])
(E/'NHJ_SOURCE_ASSOCIATION.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(status='PASS',snapshot_cases=5,route_cases=5,unbounded_instruction_length=True)))
