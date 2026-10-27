"""Exact body cuts; no external template is selected."""
from pathlib import Path
import re,hashlib,json
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/pure7';p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
raw=(e/'emission/Funs.lean.txt').read_text();start=raw.index('namespace PDict_PureSource\n')+len('namespace PDict_PureSource\n');stop=raw.index('/-- [pdict_pure::wide_c0]')
body=raw[start:stop];assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',body)
names=re.findall(r'(?m)^def\s+([\w.]+)',body);assert len(names)==11,names
header='import R1Z.ProverRwFullFuns\nset_option autoImplicit false\nnoncomputable section\nnamespace PDict_PureSource\nopen Aeneas Aeneas.Std Result ProverRwFull\n'
s=header+body+'\n'+''.join(f'\n#print axioms {n}' for n in names)+'\nend PDict_PureSource\n';(p/'PDict_PureSource.lean').write_text(s)
raw2=(e/'constants/Funs.lean.txt').read_text();body2=raw2.split('namespace PDict_ConstantsSource\n')[1].split('\nend PDict_ConstantsSource')[0]
assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',body2)
names2=re.findall(r'(?m)^def\s+([\w.]+)',body2)
s2='import Aeneas\nset_option autoImplicit false\nnamespace PDict_ConstantsSource\nopen Aeneas Aeneas.Std Result\n'+body2+'\n'+''.join(f'\n#print axioms {n}' for n in names2)+'\nend PDict_ConstantsSource\n';(p/'PDict_ConstantsSource.lean').write_text(s2)
(e/'source-cuts.json').write_text(json.dumps(dict(qualification='Exact emitted core bodies; existing ProverRwFull scalar/record representations reused. Generated headers/resource overrides omitted; namespace/imports and axiom-audit commands only. Constants from142/143 include their actual definitions;140/141 external templates remain unselected.',core_definitions=names,constant_definitions=names2,source_hashes={str(q.relative_to(r)):hashlib.sha256(q.read_bytes()).hexdigest() for q in [p/'PDict_PureSource.lean',p/'PDict_ConstantsSource.lean',e/'emission/Funs.lean.txt',e/'emission/Types.lean.txt',e/'constants/Funs.lean.txt']}),indent=2)+'\n')
