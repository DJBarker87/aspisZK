"""Disposition the original 145 *records*, without calling them 145 bodies.
Conservative records needing more source-cone work remain explicitly unresolved.
"""
from pathlib import Path
import json,hashlib,subprocess,collections
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
p=R/'evidence/pv-rdcd3-20261028/rows/V201-envelope.json';j=json.loads(p.read_text())
app={x['path']:x for x in json.loads((E/'application-sources.json').read_text())}
s=app['crates/aspis-core/src/r0/encoder.rs']['text'];b=app['crates/aspis-core/src/r0/basis.rs']['text']
assert 'q.chunks_exact(2).zip(basis)' in s
assert 'for j in 0..width.min(N - width)' in b
assert 'r0::encoder::eval_message(&coefficients[lane],z1)' in app['crates/aspis-r1-cost-probe/src/prover.rs']['text']
assert 'pub trait CodeField: Copy' in app['crates/aspis-core/src/r0/scalar.rs']['text']
lib={x['relative']:x for x in json.loads((E/'library-sources.json').read_text())}
z=lib['iter/adapters/zip.rs']['text'];a=lib['array/iter.rs']['text'];ch=lib['slice/iter.rs']['text']
assert 'unsafe impl<T, const N: usize> TrustedRandomAccessNoCoerce for IntoIter<T, N>' in a
assert 'TrustedRandomAccess for IntoIter' not in a
assert 'impl<T: Copy> NonDrop for T {}' in a
assert 'unsafe impl<\'a, T> TrustedRandomAccess for ChunksExact<\'a, T> {}' in ch
assert z.count('zip_impl_general_defaults! {}')==2
reachable={72:'Iterator::zip<ChunksExact<WideExact>, [WideExact;512]>; array IntoIterator is selected, not free zip or GenericArray::zip.',73:'Blanket IntoIterator for I: Iterator; identity on the Zip state.',87:'IntoIter.next -> PolymorphicIter.next -> MaybeUninit.assume_init_read -> as_ptr().read().',109:'ChunksExact.new/next -> split_at_unchecked -> slice::from_raw_parts.',110:'slice::from_raw_parts -> ptr::slice_from_raw_parts -> ptr::metadata::from_raw_parts.',132:'Zip Iterator::next dispatches to the NoCoerce implementation, whose next expands the general defaults macro.',134:'Iterator::zip calls Zip::new -> ZipImpl::new; NoCoerce implementation expands general defaults.',136:'basis::values<WideExact,512> calls usize::min for the inner forward range.',137:'The inner for loop uses Range<usize>::next.',138:'After each outer round, basis::double<WideExact> is called.',139:'Range<usize>::next -> TrustedStep::spec_next.'}
# Explicitly excluded alternatives of already typed method dispatch. These are
# not reachability claims about global panic/abort paths of the whole process.
excluded={133:'The application calls Iterator::zip, never the free core::iter::zip function.',135:'The stronger TrustedRandomAccess specialization requires both sides to implement that trait; array IntoIter implements only NoCoerce.',115:'ChunksExact::is_empty is not used by its next, constructor or default Zip new/next.',116:'The caller constructs ChunksExact, never RChunksExact.',117:'The encoder and basis use fixed arrays/slices; no Vec receiver is constructed in these bodies.',118:'The caller does not construct a slice Iter; ChunksExact is a distinct type.',112:'This generic slice-Iter is_empty macro alternative is not ChunksExact::next.',114:'This generic slice-Iter is_empty macro alternative is not ChunksExact::next.'}
rows=[]
for i,x in enumerate(j['unresolved']):
 f=x['function']
 if x['cohort']=='old':
  status='historical comparator only';why='This is an extractor-cohort envelope record, not a deployed 1.94.1 instantiation. Its related deployed edge is classified separately; old-body transport is not inferred.'
 elif i in reachable:status='reachable';why=reachable[i]
 elif i in excluded:status='unreachable typed alternative';why=excluded[i]
 elif f.startswith('generic_array::'):
  status='unreachable typed alternative';why='The receiver in eval_pair is ChunksExact<WideExact> zipped with [WideExact;512]; basis::values uses fixed arrays and Range<usize>. None constructs GenericArray or uses FunctionalSequence. This record was added by ambiguous method-name matching.'
 elif f.startswith('alloc::'):
  status='unreachable typed alternative';why='No BTreeMap/BTreeSet/tree node/Vec is constructed or passed in encoder/basis; this is an ambiguous Range/index method-name match.'
 elif 'core_simd' in f or 'core::splat_rt' in f:
  status='unreachable typed alternative';why='Neither field WideExact (a scalar Copy record) nor the fixed-array/slice iterator cone uses Simd pointers or Simd values. These are alternatives to scalar pointer method dispatch.'
 elif f.startswith('std::lru::') or 'core::c_str::' in f or 'core::converts::' in f:
  status='unreachable typed alternative';why='No Lru, CStr or str value is constructed or passed by encoder/basis; this candidate is an ambiguous iter/raw-parts/is_empty method-name match.'
 else:
  status='not yet resolved';why='Pointer/precondition/panic/transmute candidate requires a complete release-profile source-call path and invariant check. No exclusion or source binding is credited from the generic envelope alone.'
 rows.append(dict(record_id=f'V201-{i:03}',**x,reachability=status,argument=why,binding_status='not claimed by this reachability census'))
counts=dict(collections.Counter(x['reachability'] for x in rows));assert len(rows)==145
out=dict(row='V201',caller='aspis-r1-cost-probe::prover::opening_claim_bytes at prover.rs:354',specialization='WideExact, Message=[WideExact;1024], basis=[WideExact;512]',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=R).strip(),input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),application_snapshot_sha256=hashlib.sha256((E/'application-sources.json').read_bytes()).hexdigest(),library_snapshot_sha256=hashlib.sha256((E/'library-sources.json').read_bytes()).hexdigest(),counts=counts,records=rows,zip_dispatch='NoCoerce specialization, general defaults new/next; not the stronger TrustedRandomAccess specialization',scope='Record census, not a complete concrete call-cone certificate or whole-row restoration. Additional reached array-iterator/IndexRange bodies must be added and bound.',b3p6_1='No reclassification credited: source-only token matching does not supply a generation-receipt/hash chain to the exact extracted library body. Prior own-1 source bindings may be reused at their stated scope after closure verification.',compiler_boundary='V370/D381/D386 retained; no machine-code theorem')
(E/'v201-reachability.json').write_text(json.dumps(out,indent=2)+'\n');print(counts)
