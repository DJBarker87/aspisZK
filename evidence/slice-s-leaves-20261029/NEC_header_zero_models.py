"""Sparse all-zero binding chunks use a named symbolic guard fold permanently.
Earlier mixed-byte helpers are unchanged proved modules, not regenerated.
"""
from pathlib import Path
E=Path(__file__).resolve().parent
for number,start in [(2,32),(3,40)]:
 n=f'binding{number}';namespace=f'NEC_HeaderBinding{number}'
 s='import NEC_HeaderGuards\nimport NEC_LiveHeaderRef.Funs\nset_option autoImplicit false\nnamespace '+namespace+'\nopen Aeneas Aeneas.Std Result NEC_HeaderPredicates\n\ntheorem emitted (a : Array U8 48#usize) :\n NEC_LiveHeaderRef.'+n+'_ok a=ok (NEC_HeaderPredicates.'+n+' a) := by\n'
 for i in range(start,start+8):s+=f' have h{i} : Array.index_usize a {i}#usize=ok (byte a {i}#usize (by decide)) := byte_spec a _ (by decide)\n'
 s+=' unfold NEC_HeaderPredicates.'+n+'\n simp only [NEC_LiveHeaderRef.'+n+'_ok,'+','.join(f'h{i}' for i in range(start,start+8))+',bind_tc_ok,NEC_HeaderGuards.guarded,Bool.and_assoc]\n\n#print axioms emitted\nend '+namespace+'\n'
 (E/f'{namespace}.lean').write_text(s)
