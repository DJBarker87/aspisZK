import re,subprocess
S='/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/src/'
fp=open(S+'fp_j1.lean').read().split('\n')
start=next(i for i,l in enumerate(fp) if l.startswith('/-- [aspis_core::field::P]'))
end=next(i for i,l in enumerate(fp) if l.startswith('end PRVFresh_R1CandidateFieldParsers_j1'))
body='\n'.join(fp[start:end])
body=re.sub(r"(?<![\w./'])field\.(?!rs)", 'aspis_core.field.', body)
gate=subprocess.check_output(['git','show','research:docs/research/100bit-spend-path-20261013/evidence/lean-candidate-field-parsers-20261014/sources/R1CandidateFieldParsers.lean'],text=True).split('\n')
g0=next(i for i,l in enumerate(gate) if l.startswith('/-- Source-bound Option discriminant'))
g1=next(i for i,l in enumerate(gate) if l.startswith('  ok none') and i>g0)
hm='\n'.join(gate[g0:g1+1])
open('PRVEq_Port5Q2_ReaderWeights_t3.lean','w').write(open('PCWT_t3_head.txt').read()+hm+'\n\n'+body+'\n'+open('PCWT_t3_tail.txt').read())
