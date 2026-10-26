"""Emit compositional bounds, never concrete transcript reduction."""
from pathlib import Path
import re,sys
r=Path(__file__).resolve().parents[3];s=(r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwOrderedQuerySource.lean').read_text()
head='''import R1Z.ProverRwOrderedQuerySource
import R1Z.ProverRwOrderedBounds
set_option autoImplicit false
namespace R1Z.ProverRwOrderedQueryBounds
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwOrderedOracle ProverRwOrderedBounds
variable [ExternalTypes] [ExternalFuns]
'''
proofs=[]
for name,budget in [('absorb',1),('materializeK',17)]:
 a=re.search(r'def '+name+r'\b',s).start();a=s.index(':= do',a)+5;b=s.find('\ndef ',a);body=s[a:b if b>=0 else len(s)]
 body=body.split('end R1Z.')[0]
 binds=[]
 for c in re.split(r'(?m)(?=^  let |^  ProverRwOrderedOracle.pure |^  k )',body):
  if '←' not in c:continue
  rhs=c.split('←',1)[1].strip();kind='query' if rhs.startswith('query ') else 'absorb' if rhs.startswith('absorb ') else 'native';binds.append(kind)
 sig=f'''theorem {name} {{H : Type}} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    (ProverRwOrderedQuerySource.{name if name=='absorb' else 'materialize'} hash self row payload).history.length≤{budget} := by
  unfold ProverRwOrderedQuerySource.{name if name=='absorb' else 'materialize'}'''
 if name!='absorb':sig+=' ProverRwOrderedQuerySource.materializeK'
 left=budget;lines=[sig]
 for j,kind in enumerate(binds):
  cost=int(kind!='native');left-=cost
  lines.append(f'  apply bind_bound (n:={cost}) (m:={left})')
  lines.append('  · exact '+('absorb _ _ _ _' if kind=='absorb' else kind+'_bound _'+(' _' if kind=='query' else '')))
  lines.append(f'  · intro v{j}')
  # Nest subsequent tactics beneath this continuation, while keeping source flat.
  # indent the complete remainder in a second pass below.
 # Produce indentation by binder depth.
 out=[lines[0]];depth=0
 for j,kind in enumerate(binds):
  cost=int(kind!='native');remaining=budget-sum(int(x!='native') for x in binds[:j+1])
  pad='  '+'  '*depth
  out.append(pad+f'apply bind_bound (n:={cost}) (m:={remaining})')
  out.append(pad+'· exact '+('absorb _ _ _ _' if kind=='absorb' else kind+'_bound _'+(' _' if kind=='query' else '')))
  out.append(pad+f'· intro v{j}');depth+=1
 out.append('  '+'  '*depth+'exact pure_bound _')
 proofs.append('\n'.join(out)+f'\n#print axioms {name}\n')
t=head+'\n\n'.join(proofs)+'\nend R1Z.ProverRwOrderedQueryBounds\n';o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwOrderedQueryBounds.lean'
if '--check' in sys.argv:assert o.read_text()==t
else:o.write_text(t)
