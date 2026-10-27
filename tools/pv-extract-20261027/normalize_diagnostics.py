from pathlib import Path
import subprocess,re,hashlib,json
P=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');E=Path('evidence/pv-extract-20261027')
for op,old in [(36,'PVCBLOp36FullReference'),(224,'PVCBMOp224Raw')]:
 raw={k:subprocess.check_output(['ssh','dombarker@100.108.41.90',f'cat /home/dombarker/project-offloads/codex-pv-extract-20261027/op{op}-diagnostic-generated/{k}.lean'],text=True) for k in ['Funs','FunsExternal_Template']}
 ns=f'PV_Ext_DiagnosticOp{op}';t=raw['FunsExternal_Template'];decls=re.findall(r'\baxiom\s+([\w.]+)\s+([\s\S]*?)(?=\n/\*\*|\n/--|\Z)',t)
 fields=[]
 for i,(name,ty) in enumerate(decls):
  ty=ty.strip();fields.append((name,ty))
 ext=f'import R1Z.{ns}Types\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnamespace {ns}\nclass ExternalFuns where\n'
 for i,(name,ty) in enumerate(fields):ext+=f'  op{i} '+ty.replace('\n','\n  ')+'\n'
 for i,(name,ty) in enumerate(fields):ext+=f'abbrev {name} [ext : ExternalFuns] := @ExternalFuns.op{i} ext\n'
 ext+=f'end {ns}\n';(P/f'{ns}External.lean').write_text(ext)
 s=raw['Funs'].replace(f'import {old}.Types',f'import R1Z.{ns}Types').replace(f'import {old}.FunsExternal',f'import R1Z.{ns}External').replace(f'namespace {ns}',f'namespace {ns}\nvariable [ExternalFuns]',1)
 (P/f'{ns}Funs.lean').write_text(s)
 (E/f'op{op}-normalization.json').write_text(json.dumps(dict(raw_hashes={k:hashlib.sha256(v.encode()).hexdigest() for k,v in raw.items()},external_parameters=[name for name,ty in fields],adaptation='Generated opaque declarations made explicit typeclass parameters; imports changed to own PV_Ext modules; emitted function bodies unchanged. Diagnostic typechecking only, no source law.'),indent=2)+'\n')
