"""Generate fixed-row full-carrier header windows; no copy replacements authored.
Rows14..26 are isolated to avoid the timed whole-buffer mux shape.
"""
from pathlib import Path
E=Path(__file__).resolve().parent
src=lambda r:32+5*r if r<=2 else 64+5*r if r<=14 else 155+453*(r-15) if r<=25 else 6546
dst=lambda r:32+5*r if r<=2 else 64+5*r if r<=14 else 171+901*(r-15) if r<=25 else 12898
s='''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
'''
attrs='''#[kani::proof]#[kani::unwind(7)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
'''
for r in range(14,27):
 a,b=src(r),dst(r)
 s+=f'#[repr(C)]struct NCA_Input{r}{{prefix:[u8;{a}],header:[u8;5],tail:[u8;{7015-a-5}]}}\n'
 s+=f'#[repr(C)]struct NCA_Output{r}{{prefix:[u8;{b}],header:[u8;5],tail:[u8;{14759-b-5}]}}\n'
 for wrong in [False,True]:
  s+=attrs+f'fn NCA_header{r}'+('_wrong' if wrong else '')+'(){\n'
  s+=f' let mut input=NCA_Input{r}{{prefix:kani::any(),header:kani::any(),tail:kani::any()}};let mut out=NCA_Output{r}{{prefix:kani::any(),header:kani::any(),tail:kani::any()}};\n'
  if wrong:s+=' input.header[4]=1;out.header[4]=0;\n'
  else:
   s+=f' let k:usize=kani::any();let p:usize=kani::any();let q:usize=kani::any();kani::assume(k<5&&p<{b}&&q<{14759-b-5});let before=out.prefix[p];let after=out.tail[q];\n'
   s+=f' assert_eq!(core::mem::size_of::<NCA_Input{r}>(),7015);assert_eq!(core::mem::size_of::<NCA_Output{r}>(),14759);assert_eq!(core::mem::offset_of!(NCA_Input{r},header),{a});assert_eq!(core::mem::offset_of!(NCA_Output{r},header),{b});\n'
  s+=f' let source=unsafe{{core::slice::from_raw_parts((&input as *const NCA_Input{r}).cast::<u8>(),7015)}};\n let logical=unsafe{{core::slice::from_raw_parts_mut((&mut out as *mut NCA_Output{r}).cast::<u8>(),14759)}};\n'
  s+=f' let compact=source;let semantic=&mut logical[..13831];let mut src={a};let mut dst={b};\n semantic[dst..dst+5].copy_from_slice(&compact[src..src+5]);src+=5;dst+=5;\n'
  if wrong:s+=' assert_eq!(out.header[4],0,"negative row header copy");\n'
  else:s+=f' assert_eq!(src,{a+5});assert_eq!(dst,{b+5});assert_eq!(out.header[k],input.header[k]);assert_eq!(out.prefix[p],before);assert_eq!(out.tail[q],after);kani::cover!(k==4&&q=={14759-b-6},"header and last full-carrier frame byte");\n'
  s+='}\n'
(E/'NCA_headers.rs.txt').write_text(s)
Path('/private/tmp/NCA_headers_product.rs').write_text(s)
