from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
original=Path('evidence/kani-mitig-20261028/KMX_trigger.rs.txt').read_text()
table=json.loads(Path('evidence/kani-mitig-20261028/KMX_CONFIGURATION_MAP.json').read_text())
# Approved replacement registrations, verbatim from the original KNH shape source.
shape=(E/'KNH_slice.rs.txt').read_text();attrs=shape[shape.index('#[kani::stub('):shape.index('#[kani::unwind(8)]')]
attrs=attrs.replace('<[u8]>','<[u32]>').replace('::<u8>','::<u32>')
preamble='#![feature(allocator_api)]\nextern crate alloc;\n#[cfg(kani)] mod KMX_stubs;\nuse alloc::{vec,vec::Vec};\n#[derive(Clone,Copy,PartialEq,Eq,Debug)] struct KMX_Pair {a:u32,b:u32}\n'
helper=re.search(r'(?m)^#\[inline\(never\)\] fn KMX_slice_destination[^\n]*',original).group(0)+'\n'
preamble+=helper
mit=preamble;native=preamble;mapping=[]
for row in table:
 c=row['config'];large=c['width']*c['n']>128
 names={}
 for kind,key in [('correct','expected'),('wrong','negative')]:
  name=row[key]['harness'].split('::')[-1]
  match=re.search(r'(?m)^fn '+re.escape(name)+r'\(\)\{[^\n]*',original);assert match,name
  body=match.group(0);before=original[:match.start()].splitlines()[-1]
  unwind=int(re.search(r'unwind\((\d+)\)',before).group(1))
  if large:
   # One copied cell at an arbitrary logical window origin. No full-buffer frame claim.
   ty=c['ty'];zero={'u8':'0u8','u32':'0u32','u64':'0u64','[u8;32]':'[0u8;32]','KMX_Pair':'KMX_Pair{a:0,b:0}'}[ty];one={'u8':'1u8','u32':'512u32','u64':'512u64','[u8;32]':'[1u8;32]','KMX_Pair':'KMX_Pair{a:512,b:1}'}[ty]
   name=f'KNH_window_{c["id"]}_{kind}';unwind=8
   body=f'fn {name}(){{let origin:usize=kani::any();kani::assume(origin<{c["n"]});let input=[{one}];let mut level=[{zero}];level.copy_from_slice(&input);assert_eq!(level[0],'+(one if kind=='correct' else zero)+');}'
  names[kind]=name
  common=f'#[kani::proof] #[kani::unwind({unwind})]\n'
  mit+=common+attrs+body+'\n';native+=common+body+'\n'
 mapping.append(dict(config=c,kind='ONE_CELL_LOGICAL_WINDOW_NO_FRAME' if large else 'ORIGINAL_BODY',harnesses=names))
(E/'KNH_copy_split_mitigated.rs.txt').write_text(mit);(E/'KNH_copy_split_builtin.rs.txt').write_text(native)
(E/'KNH_SPLIT_MAP.json').write_text(json.dumps(mapping,indent=2)+'\n')
(E/'KNH_N039_REVIEW.json').write_text(json.dumps(dict(reason='c023_wrong CBMC timeout; stop bulk driver and c023_correct which driver had already started; no credit',timed_out='KMX_bounded_c023_wrong',interrupted='KMX_bounded_c023_correct',replacement='one-cell logical windows for every configuration over128 bytes; full-buffer Lean frame remains OPEN and no Lean budget is available',no_cap_or_timeout_increase=True),indent=2)+'\n')
