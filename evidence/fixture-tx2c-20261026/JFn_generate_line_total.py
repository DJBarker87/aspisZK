from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2]
text=(R/'lean/SAQ_LineSource.lean').read_text().split('def line\n',1)[1].split('\nstructure Cuts',1)[0]
# Mirror the exact straight-line source call order, reusing generic totality.
s='''import JFn_ScaleTotal
import SAQ_LineSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_LineTotal
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof

theorem source (alpha a b c d : E) (ix iy lx ly lz : U32)
    (hAlpha : CanonicalWide alpha) (ha : CanonicalWide a) (hb : CanonicalWide b)
    (hc : CanonicalWide c) (hd : CanonicalWide d) :
    ∃ out, SAQ_LineSource.line alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz])=ok out ∧ CanonicalWide out := by
'''
canon={'alpha':'hAlpha','a1':'ha','b':'hb','c':'hc','d':'hd'}
args={'quarter':'SAQ_LineSource.quarter','iz':'lz','ix':'lx','iy':'ly','a1':'a'}
body=text.split('  let we ←',1)[1]
body='  let we ←'+body
body=body.replace('  field.wide_exact.WideExact.add h0 we13','  let out ← field.wide_exact.WideExact.add h0 we13')
body=re.sub(r'←\s*\n\s*','← ',body)
calls=[]
for var,op,parameters in re.findall(r'let (\w+) ← (field\.[\w.]+) ([^\n]+)',body):
 ps=[args.get(x,x) for x in parameters.split()]
 if op=='field.M31.mul':
  s+=f'  obtain ⟨{var},H{var}⟩ := JFn_ScaleTotal.base {" ".join(ps)}\n'
 elif op.endswith('mul_m31'):
  s+=f'  obtain ⟨{var},H{var},C{var}⟩ := JFn_ScaleTotal.wide {" ".join(ps)}\n'
  canon[var]='C'+var
 else:
  method=op.rsplit('.',1)[1]
  s+=f'  obtain ⟨{var},H{var},C{var},_⟩ := wide_{method}_total_exact {" ".join(ps)} {canon.get(parameters.split()[0],"BAD")} {canon.get(parameters.split()[1],"BAD")}\n'
  canon[var]='C'+var
 calls.append('H'+var)
s+='  refine ⟨out,?_,Cout⟩\n'
for j,name in enumerate(['a','b','c','d']):
 s+=f'  have ia{j} : Array.index_usize (Array.make 4#usize [a,b,c,d]) {j}#usize=ok {name} := rfl\n'
for j,name in [(2,'lx'),(3,'ly'),(4,'lz')]:
 s+=f'  have ii{j} : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) {j}#usize=ok {name} := rfl\n'
s+='  simp only [SAQ_LineSource.line,ia0,ia1,ia2,ia3,ii2,ii3,ii4,'+','.join(calls)+',bind_tc_ok]\n'
s+='\n#print axioms source\nend AspisR1.JFn_LineTotal\nend\n'
assert 'BAD' not in s
f=R/'lean/JFn_LineTotal.lean'
if '--check' in sys.argv: assert f.read_text()==s
else:f.write_text(s)
