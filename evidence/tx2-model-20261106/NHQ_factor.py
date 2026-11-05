"""Split inherited continuation at exact syntactic callee returns, no body edits."""
from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NHQ_Tx2CommonModel.lean';s=p.read_text()
start=s.index('def afterResume');end=s.index('\ndef run',start);body=s[start:end];defs=[]
header='''(ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (obs : Option (verifier.Phase → Result Unit)) (inactive : aspis_core.field.wide_exact.WideExact)
 (round0 folded round1 : Usize)'''
# exact continuation after query_loop; all preceding values stay explicit
lines=body.splitlines(True);idx=next(i for i,l in enumerate(lines) if 'let cf5 ←' in l);indent=len(lines[idx])-len(lines[idx].lstrip());last=idx+1
while last<len(lines) and (not lines[last].strip() or len(lines[last])-len(lines[last].lstrip())>=indent):last+=1
fragment=''.join(l[indent:] if l.strip() else l for l in lines[idx:last])
fragment=fragment.replace('r6','reply').replace('val1','inactive').replace('i2','round0').replace('i3','folded').replace('i4','round1')
defs.append('def afterQuery '+header+'\n (reply : R (verifier.Accumulator × verifier.BatchedWeights)) : Result (R Unit) := do\n'+''.join(' '+l if l.strip() else l for l in fragment.splitlines(True)))
lines[idx:last]=[' '*indent+'afterQuery ops proof p obs val1 i2 i3 i4 r6\n'];body=''.join(lines)
s=s[:start]+'\n'.join(defs)+'\n'+body+s[end:]
# source remains definitional and resume API unchanged
pos=s.index('#print axioms source')
s=s[:pos]+'''theorem query_error (p : verifier.Prepared)
 (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 : Usize)
 (error : verifier.Error) :
 afterQuery ops proof p obs inactive round0 folded round1 (.Err error) = ok (.Err error) := by rfl

#print axioms query_error
'''+s[pos:]
p.write_text(s)
