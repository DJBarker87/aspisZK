from pathlib import Path
import re,sys
root=Path(__file__).resolve().parents[2];b=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(root/'evidence/pv-cblib-20261027/drafts/PV_CBL_FallbackBlockFactored.lean.txt').read_text()
s=s.replace('PV_CBL_FallbackBlockFactored','PV_CBL_BlockValueFactored')
s=s[:s.index('theorem source')]+'''/-- Congruence inspects one bind at a time, never a 64-round arithmetic term. -/
theorem bind_ext {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a = g a) : (r >>= f) = (r >>= g) := congrArg (fun k => r >>= k) (funext h)
theorem source (state : Array U32 8#usize) (input : Array U32 16#usize) :
    PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state input = block state input := by
'''
src=(b/'PV_CBL_FallbackBlock.lean').read_text();a=src.index('  let i ← Array.index_usize state 0#usize',src.index('def sha_fallback_reference.sha256_digest_block_u32'));z=src.index('\n/-- [pv_cblib_source::sha_fallback_reference::extracted_block]');body=src[a:z]
ms=list(re.finditer(r'(?:^|\n)\s*let (\w+) ←\s*',body))
for i,m in enumerate(ms):
 exp=' '.join(body[m.end():(ms[i+1].start() if i+1<len(ms) else len(body))].split())
 if exp.startswith('sha_fallback_reference.add '):s+='  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]\n'
 s+=f'  apply bind_ext\n  intro {m[1]}\n'
s+='  rfl\n#print axioms bind_ext\n#print axioms source\nend R1Z.PV_CBL_BlockValueFactored\n'
a=s.index('/-- Congruence');z=s.index('theorem source',a);s=s[:a]+s[z:]
s=s.replace('import R1Z.PV_CBL_FallbackFourBind','import R1Z.PV_CBL_FallbackFourBind\nimport R1Z.PV_CBL_BlockBindExt').replace('  apply bind_ext','  apply PV_CBL_BlockBindExt.bind_ext').replace('#print axioms bind_ext\n','')
p=b/'PV_CBL_BlockValueFactored.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('symbolic binds',len(ms))
