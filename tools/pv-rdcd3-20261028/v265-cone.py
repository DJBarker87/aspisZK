"""Associate concrete source dispatch with every conservative unresolved record.
Run locally after collecting source gates. Does not grant credit from counts.
"""
from pathlib import Path
import hashlib,json,lzma
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-rdcd3-20261028'
prior=R/'evidence/pv-rdcd-20261028/typed-reached-static.json.xz'
row=next(x for x in json.loads(lzma.open(prior).read()) if x['id']=='V265')
records=[]
for n,x in enumerate(row['unresolved']):
 f=x['function'];call=x['call']
 if f.startswith('alloc::'):
  state='excluded concrete dispatch'
  why='The only source range has type core::ops::Range<usize>. No BTreeMap, BTreeSet, node, leaf, key/value storage or associated iterator exists in the complete checked square_n/sampler bodies. These candidates enter only through the ambiguous printed name Range; substituting one would change the receiver type.'
  law='range-source-result.json dispatch_checks; v265-source-result.json complete square_n body'
 elif '::spec_next' in call:
  state='concrete source law'
  why='usize implements TrustedStep, selecting the specialized ops::Range<T> implementation; no generic fallback is instantiated.'
  law='Range194.extracted/projection; RangeFold.next_active/next_empty/increment_bound'
 elif 'Range<usize> as Iterator>::next' in call:
  state='concrete source law'
  why='Receiver is ops::Range<usize>, not either allocation-tree Range. Blanket IntoIterator returns the full iterator state unchanged.'
  law='Range194.projection; RangeLoop.all_endpoints; Control194.intoIter_state'
 elif 'panic_impl' in call:
  state='terminal Result projection only'
  why='Actual invalid array indexing remains an error at the retained Aeneas Result interface. No continuation runs. Panic diagnostics and whole-observer behavior are not established by this interface. M31 inverse zero assertion remains an explicit terminal failure; no successful inverse is assumed.'
  law='Index194.failure/nested_failure; V265Inverse.source (zero assertion retained); Control194.prior_failure/panic_terminal; Result194.question_mark'
 elif 'str>::len' in call:
  state='panic diagnostic outside Result projection'
  why='The fmt Arguments/str length call belongs to panic construction, not successful arithmetic, lookup or folding. The Result theorem preserves the terminal error, not diagnostic bytes, allocations, timing or observer behavior; no native RunJoin/observer credit.'
  law='Control194.panic_terminal; Index194.failure; scope restriction retained explicitly'
 else:raise AssertionError(x)
 records.append(dict(index=n,**x,disposition=state,argument=why,evidence=law))
assert len(records)==18
source={}
for name in ['range-source-result.json','library-source-result.json','v265-source-result.json']:
 p=E/name;source[name]=hashlib.sha256(p.read_bytes()).hexdigest()
j=dict(row='V265',conservative_input_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),unresolved_disposition=records,source_gates=source,
 scope='Complete value/Result structural association is still conditional on all named Lean receipts and frozen DAG. No binary, panic-diagnostic, world or observer theorem. No claim that conservative counts are a monomorphized call graph.',
 concrete_library_methods=['ops::Range<usize>::next','RangeIteratorImpl<usize>::spec_next','Step<usize>::forward_unchecked','usize::unchecked_add (increment one)','Iterator::fold<Range<usize>>','IntoIterator<Iterator>::into_iter','[T;N]::index<usize>','[T]::index<usize>','SliceIndex<[T]><usize>::index','u32/u64::wrapping_add','u32::wrapping_sub','u64::wrapping_mul','u16/u64::wrapping_shr','u64::wrapping_shl','u16/u64::unchecked_shr','u64::unchecked_shl','Result::branch/from_residual/unwrap_or_else; Option::ok_or; concrete identity error conversion; lossless widening; array writeback; endian decode'],
 compiler_primitives='Integer intrinsics, casts, immutable backing storage reads and terminal panic projection retain the existing compiler/Aeneas semantic trust. Reclassification within existing tool trust; no endpoint premise removal.',
 rejected_alternatives=['BTreeMap Range','BTreeSet Range','core::range::Range (distinct from core::ops::Range)','aspis_statement::Variant equality (actual receiver is transport::Variant)'],
 qualification='A source pattern gate is not a recovered original checker. Every scope qualification is retained; diagnostics/observer obligations remain open.')
(E/'v265-cone-disposition.json').write_text(json.dumps(j,indent=2)+'\n')
print('18 conservative records dispositioned at the explicitly restricted Result boundary; no row status set')
