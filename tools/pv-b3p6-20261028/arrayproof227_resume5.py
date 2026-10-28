"""Port implicit literal-size proofs to symbolic cons-length proofs.
The data expression, order, and literal values are unchanged. Only the proof
argument to Array.make is supplied explicitly; proof irrelevance applies.
"""
from pathlib import Path
import re,json,hashlib
D=Path('evidence/pv-b3p6-20261028');p=D/'ported227-complete-resume5.lean.txt';s=p.read_text();start=s.index('/-- [pv_b3p6_reference227::reference_copy_terminal::constants::COPY_PATTERNS]');changes=[]
for m in re.finditer(r'Array\.make\s+\d+#usize\s+\[',s[start:]):
 a=start+m.start();b=start+m.end();depth=1;i=b
 while depth:
  depth+=(s[i]=='[')-(s[i]==']');i+=1
 changes.append(i)
for i in sorted(changes,reverse=True):s=s[:i]+' (by simp only [List.length_cons, List.length_nil]; rfl)'+s[i:]
q=D/'ported227-arrayproof-resume5.lean.txt';q.write_text(s)
(D/'arrayproof227-resume5.json').write_text(json.dumps(dict(input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),proof_arguments=len(changes),data_edits=False,reason='42027 controlled SIGTERM after COPY_PATTERNS RSS8791936KiB; expose literal length proof with symbolic List.length_cons/length_nil instead of implicit default tactic',unchanged_prefix='first six declaration chunks'),indent=2)+'\n')
print(len(changes))
