from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[2]
s=(D/'generated/Funs.lean').read_text();a=s.index('def retry_attempt\n');b=s.index('\npartial_fixpoint',a);f=s[a:b]
header,body=f.split('  := do\n',1)
header=header.replace('def retry_attempt','def retry_step').replace('Result (Tape × N × L × B × (core.result.Result RetriedProof Error))','Result (ControlFlow (Tape × N × L × B × Std.Usize)\n    (Tape × N × L × B × (core.result.Result RetriedProof Error)))')
a=body.index('          retry_attempt ');b=body.index('\n        | Error.AttemptsExhausted',a)
body=body[:a]+'          ok (cont (tape1, proof_account1, after_store, body1, i))'+body[b:]
i=0
while True:
 a=body.find('ok (',i)
 if a<0:break
 if body[a+4:].startswith('cont '):i=a+4;continue
 start=a+3;depth=0;j=start
 while j<len(body):
  if body[j]=='(':depth+=1
  elif body[j]==')':
   depth-=1
   if depth==0:break
  j+=1
 body=body[:a]+'ok (done '+body[start:j+1]+')'+body[j+1:];i=j+11
expected=(header+'  := do\n'+body).replace('U64) Error)))','U64) ProverRwRngCaller.Error)))').replace('RetriedProof Error)))','RetriedProof ProverRwRngCaller.Error)))')
p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwRngCallerStep.lean';actual=p.read_text().split('def retry_step',1)[1].split('\n\ntheorem retry_factor',1)[0]
assert ('def retry_step'+actual).strip()==expected.strip()
print('concrete source step cut checked',hashlib.sha256(expected.encode()).hexdigest())
