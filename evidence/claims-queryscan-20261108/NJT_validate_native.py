"""Read-only source/certificate association. No proof or native compiler launch."""
from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
sha=lambda data:hashlib.sha256(data).hexdigest()
def blob(p):return subprocess.check_output(['git','show',REV+':'+p])
semantic=blob('crates/aspis-r1-cost-probe/src/r1_semantic.rs').decode()
original=semantic[semantic.index('fn claims('):semantic.index('\n#[inline(never)]',semantic.index('fn claims('))]
ref=(E/'NJT_claims_ref.rs.txt').read_text()
expected='''fn claims(prefix: &Prefix<'_>) -> Result<Box<[[QM31; 29]; 3]>, Error> {
    let record = prefix.validated_record(25)?;
    let mut out =
        aspis_core::r0::heap::uninit::<[[QM31; 29]; 3]>().map_err(|_| Error::Allocation)?;
    unsafe {
        for p in 0..3 {
            out.as_mut_ptr()
                .cast::<[QM31; 29]>()
                .add(p)
                .write(record.decode_k::<29>(p * 29)?);
        }
        Ok(out.assume_init())
    }
}
'''
assert original.strip()==expected.strip()
heap=blob('crates/aspis-core/src/r0/heap.rs').decode()
assert 'out.try_reserve_exact(n).map_err(|_| Error::Allocation)?' in heap
assert 'out.try_reserve_exact(1).map_err(|_| Error::Allocation)?' in heap
assert 'out.resize(n, value)' in heap and 'out.set_len(1)' in heap
assert [int(n) for n in re.findall(r'decode_k::<29>\((\d+)\)',ref)]==[0,29,58]
assert 'let value = [row0, row1, row2]' in ref and 'heap::filled(1, value)' in ref
assert 'out[0][' not in ref and 'for ' not in ref
pins=json.loads((E/'NJT_EXTRACTION_PINS.json').read_text())
assert pins['charon_exit']==pins['aeneas_exit']==0
assert sha(ref.encode())==pins['reference']['reference']
assert pins['lock_before']==pins['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
raw=(E/'NJT_emitted/raw/NJT_ClaimsRef/Funs.lean').read_text()
adapted=(E/'NJT_ClaimsRef_Funs.lean').read_text()
assert adapted==raw.replace('import NJT_ClaimsRef.Types','import NJT_ClaimsRef_Types').replace('import NJT_ClaimsRef.FunsExternal','import NJT_ClaimsRef_External')
assert sha((E/'NJT_KMX.patch').read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
runs=[]
for a in ['NJT_K003','NJT_K004','NJT_K005','NJT_K006','NJT_K007','NJT_K008','NJT_K009']:
 r=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text();positive=a in ['NJT_K003','NJT_K006','NJT_K008']
 assert ('VERIFICATION:- SUCCESSFUL' if positive else 'VERIFICATION:- FAILED') in out
 assert r['exit_status']==(0 if positive else 1)
 graph=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text())
 assert graph['graph_matches_frozen'] and lock['unchanged']
 assert lock['before']==lock['after']==pins['lock_before']
 runs.append(dict(attempt=a,module=r['module'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],classification='PASS' if positive else 'MATCHED_ASSERTION_FAILURE'))
for name in ['NJT_claims_carrier.rs.txt','NJT_resize_window.rs.txt','NJT_allocation_cut.rs.txt']:
 s=(E/name).read_text();assert not re.search(r'\bstatic\b|Option\s*<\s*fn|kani::assume\([^)]*==',s)
unchanged={}
for path in ['crates','programs','Cargo.lock']:
 a=subprocess.check_output(['git','rev-parse',REV+':'+path],text=True).strip();b=subprocess.check_output(['git','rev-parse','HEAD:'+path],text=True).strip();assert a==b
 unchanged[path]=a
mutations=[original.replace('.add(p)','.add(p+1)'),original.replace('uninit::<','uninit_changed::<'),original.replace('p * 29','p * 28')]
assert all(m.strip()!=expected.strip() for m in mutations)
report=dict(target_not_yet_established=True,frozen_revision=REV,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),frozen_claims_sha256=sha(original.encode()),source_identity_mutations_rejected=len(mutations),reference_sha256=sha(ref.encode()),raw_emitted_body_unchanged_except_imports=True,source_trees=unchanged,runs=runs,allocator='Existing Allocator returning/abort semantics; numeric request1x1392 align4, no user-visible aliases; caller canonicality excludes decode errors before allocator reordering',scope='P6 hybrid source/cut association, not a cold source-to-ELF replay',reused=['NJM_K006/K007/K008','NJM_K011/K012','NJG_K024/K025','NJG_K026/K027','KMX_CopyMeaning','NJG_RowPrefixes'],complete129=False,remaining='Unsafe P6 allocator/Std whole Result+heap-state instantiation is OPEN; returning-success std is only a value interpretation',pending='Next ledger gate for four QueryScan candidates')
(E/'NJT_NATIVE_VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
print('NJT native source/cut checks PASS')
