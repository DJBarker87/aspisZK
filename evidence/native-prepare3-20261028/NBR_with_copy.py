"""Add the merged KMX replacement bodies (prefix-only renaming) to own gates."""
from pathlib import Path
import sys
source=Path(sys.argv[1]).read_text()
stubs=Path('/private/tmp/NBR_copy_stubs.rs').read_text()
attrs='''#[kani::stub(<[u8]>::copy_from_slice,NBR_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,NBR_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,NBR_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,NBR_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,NBR_to_vec)]
#[kani::stub(alloc::alloc::realloc,NBR_realloc)]
'''
source=source.replace('use super::*;','use super::*;\n'+stubs,1)
if '#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,NBR_extend_cut)]' in source:
 attrs=attrs.replace('#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,NBR_extend_from_slice)]\n','')
source=source.replace('#[kani::proof]',attrs+'#[kani::proof]')
if len(sys.argv)>2:
 import re
 source=re.sub(r'#\[kani::unwind\(\d+\)\]','#[kani::unwind('+sys.argv[2]+')]',source)
Path('/private/tmp/NBR_candidate.rs').write_text(source)
