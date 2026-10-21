"""Emit direct Result case inversion, avoiding higher-order unification."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]
base=root/'docs/research/100bit-spend-path-20261013/lean'
p=base/'OraclePortCkptAbiSourceFields.lean'
s=p.read_text()
a=s.index('  obtain ⟨⟨state,rState⟩')
end=s[s.index('  have finalEq :='):]
head=s[:a]
lines=[]
indent=2
simp='core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok'
def put(t): lines.append(' '*indent+t)
def branch(result,value):
 global indent
 put(f'cases {result} with')
 put('| Err e =>')
 indent+=2
 put('conv at h => lhs; whnf')
 put('cases h')
 indent-=2
 put(f'| Ok {value} =>')
 indent+=2
 put('conv at h => lhs; whnf')
def read(value,reader):
 put(f'obtain ⟨⟨{value}Result,{reader}⟩,{value}Read,h⟩ := bind_success _ _ _ h')
 branch(value+'Result',value)
for value,reader in [('state','rState'),('root0','rRoot0'),('root1','rRoot1')]:
 put(f'obtain ⟨⟨{value},{reader}⟩,{value}Read,h⟩ := bind_success _ _ _ h')
for value,reader in [('gamma','rGamma'),('kappa','rKappa'),('alpha0','rAlpha0'),('alpha1','rAlpha1'),('rho','rRho')]:read(value,reader)
for i in range(22):
 put(f'obtain ⟨⟨qb{i},rq{i}⟩,qr{i},h⟩ := bind_success _ _ _ h')
 put(f'obtain ⟨q{i},qd{i},h⟩ := bind_success _ _ _ h')
put('obtain ⟨validated,validate,h⟩ := bind_success _ _ _ h')
branch('validated','validUnit')
put('cases validUnit')
put('obtain ⟨semanticResult,semanticCall,h⟩ := bind_success _ _ _ h')
branch('semanticResult','semanticPair')
put('rcases semanticPair with ⟨semanticAlpha,semanticEnd⟩')
for value,reader in [('x0','rX0'),('y0','rY0'),('x1','rX1'),('y1','rY1'),('claim','rClaim'),('rhs','rRhs'),('power','rPower')]:read(value,reader)
put('obtain ⟨finalLength,lengthCall,h⟩ := bind_success _ _ _ h')
put('obtain ⟨zero,zeroCall,h⟩ := bind_success _ _ _ h')
put('obtain ⟨allocatedResult,allocatedCall,h⟩ := bind_success _ _ _ h')
branch('allocatedResult','allocated')
put('obtain ⟨weightsResult,weightsCall,h⟩ := bind_success _ _ _ h')
branch('weightsResult','weightsPair')
put('rcases weightsPair with ⟨weights,finalAt⟩')
put('obtain ⟨cursor,h⟩ := checkpoint_guard _ _ _ h')
put('have cursorEq : finalAt = end1 := by simpa only [bne_eq_false_iff_eq] using cursor')
put('obtain ⟨next,nextCast,h⟩ := bind_success _ _ _ h')
# Preserve the existing explicit output-construction and query-chain proof.
proof,audits=end.split('\n#print axioms',1)
for line in proof.splitlines():
 lines.append(' '*indent+line[2:] if line.startswith('  ') else line)
output=head+'\n'.join(lines)+'\n\n#print axioms'+audits
p.write_text(output)
