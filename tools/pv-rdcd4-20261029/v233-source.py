"""V233 concrete Eager source/representation census, not a native checker."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029';deps={(x['crate'],x['relative']):x for x in json.load(open(E/'buffer-dependency-sources.json'))}
lex=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.S)
def tokens(s):return [m[0] for m in lex.finditer(s) if not m[0].startswith(('//','/*'))]
def span(s,ctx,marker):
 assert s.count(ctx)==1,ctx;a=s.index(marker,s.index(ctx));b=s.index('{',a);d=0
 for m in lex.finditer(s,b):
  if m[0]=='{':d+=1
  elif m[0]=='}':
   d-=1
   if not d:return s[a:m.end()]
 raise AssertionError(marker)
sealed=deps['block-buffer-0.10.4','sealed.rs'];body=span(sealed['text'],'impl Sealed for super::Eager','fn split_blocks<')
expected='''fn split_blocks<N:ArrayLength<u8>>(data:&[u8])->(&[Block<N>],&[u8]){let nb=data.len()/N::USIZE;let blocks_len=nb*N::USIZE;let tail_len=data.len()-blocks_len;unsafe{let blocks_ptr=data.as_ptr()as*const Block<N>;let tail_ptr=data.as_ptr().add(blocks_len);(slice::from_raw_parts(blocks_ptr,nb),slice::from_raw_parts(tail_ptr,tail_len),)}}'''
assert tokens(body)==tokens(expected)
g=deps['generic-array-0.14.7','lib.rs'];layouts=[]
for marker,fields,repr_ in [('pub struct GenericArrayImplEven<T, U>','{parent1:U,parent2:U,_marker:PhantomData<T>,}','C'),('pub struct GenericArrayImplOdd<T, U>','{parent1:U,parent2:U,data:T,}','C'),('pub struct GenericArray<T, U: ArrayLength<T>>','{data:U::ArrayType,}','transparent')]:
 actual=span(g['text'],marker,marker);assert tokens(actual[actual.index('{'):])==tokens(fields),marker
 before=g['text'][:g['text'].index(marker)];assert '#[repr('+repr_+')]' in before[-180:],marker
 layouts.append(dict(marker=marker,body=actual,repr=repr_,file_sha256=g['sha256'],model='LibraryShapes Even/Odd/GenericArray; BlockLayout194.size_power/size64; BlockCodec.flatten_encode'))
env=json.load(open(R/'evidence/pv-rdcd3-20261028/rows/V233-envelope.json'));records=[]
for i,x in enumerate(env['unresolved']):
 if i<30:disposition='historical comparator; not a deployed body'
 elif i in [30,31,32,33]:disposition='reached raw-slice/metadata forwarding body, concrete [GenericArray<u8,U64>] or [u8]'
 elif i in [39,49,56]:disposition='guard-excluded panic/format diagnostic: nonzero constant64, valid typed input, debug/UB checks inactive'
 elif i in [50,51,52,57]:disposition='typed-excluded SIMD vector receiver; Eager only uses scalar u8/raw slice pointers'
 elif i==60:disposition='typed-excluded str metadata constructor; actual targets are [u8] and [GenericArray<u8,U64>]'
 elif i in [40,41,42,43,44,45,46,47,48]:disposition='excluded transmute_copy/read/read_unaligned expansion: root performs no pointee reads; pointer-value addr precondition path inactive, other candidate receiver bodies not called'
 else:disposition='guard-excluded null/dangling/addr/alignment precondition helper; released raw constructors and valid in-allocation u8 add do not execute this check'
 records.append(dict(index=i,record=x,disposition=disposition))
# The same complete raw-slice source wrappers were checked for V201; their
# shared generic source bodies do not change with the concrete element type.
bind=json.load(open(E/'v201-source-bindings.json'))
old=json.load(open(R/'evidence/pv-rdcd-20261028/original-gates-recovered/results.json'))
entry=next(x for x in old['results'] if 'V233' in x['rows']);assert entry['result']=='PASS'
out=dict(row='V233',records=records,counts=dict(historical=30,reached=4,excluded_guard_or_typed=27),deployed_body=dict(path=sealed['path'],file_sha256=sealed['sha256'],body=body,expected=expected),layout_records=layouts,primitive_bindings=['PV_RDCD4_Memory194.raw_parts_forward/metadata_forward/raw_parts_fields/length','PV_RDCD4_BlockLayout194.bounded/remainder/tail_bound/word_bounds','PV_RDCD4_V233.source_reference/aliases/valid_tail','PV_AL_BlockCodec.flatten_encode; SplitCarrier.block_bytes/tail_bytes; SplitSelected.consumed'],source_steps=['N::USIZE64 is a fixed type constant, discharged by current-cohort SplitNativeShape.native_size','divide n by64; multiply quotient by64 bounded by n; tail subtraction exact, no word overflow','block pointer cast preserves base and origin, alignment1 and64-byte repr(C) storage at retained V370 layout boundary','tail pointer advances exactly consumed bytes in the same live immutable input allocation','from_raw_parts preserves pointer and supplied count/length; both views retain input lifetime; no reads, stores, allocation, drop or user callbacks','semantic projection groups the original bytes into the original GenericArray storage carrier without allocating a native copy; alias coordinates are proved separately'],original_checker=entry,scope='Own-1 source/value/Result plus logical alias-coordinate transport; compiler/runtime layout and machine addresses remain V370/D381/D386. Old66064 pairs remain finite validation.',b3p6_1_reclassifications=0,pending='Fresh current-cohort selected callback, BlockLayout194 and V233 root plus complete coherent source/object check required.')
(E/'v233-source-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print('V233:61 records dispositioned;4 reached raw constructors; complete Eager body and three repr declarations checked. Kernel/root closure pending.')
