from pathlib import Path
import re,sys
D=Path(__file__).resolve().parent
stem=sys.argv[1];skip=sys.argv[2]
p=D/'lean'/(stem+'.lean');s=p.read_text();end='end '+stem+'\n';assert s.endswith(end)
s=s[:-len(end)]
fields=re.findall(r'^  (op\d+)(?:\s|\{|\()',Path('docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean').read_text(),re.M)
for f in fields:
 if f==skip:continue
 s+=f'theorem preserved_{f} [ExternalTypes] (ops : ExternalFuns) :\n    @ExternalFuns.{f} _ (selected ops) = @ExternalFuns.{f} _ ops := rfl\n#print axioms preserved_{f}\n'
p.write_text(s+end)
