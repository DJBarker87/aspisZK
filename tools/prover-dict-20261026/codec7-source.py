from pathlib import Path
import re,hashlib,json
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/pure7/codec';p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_CodecSource.lean';raw=(e/'Funs.lean.txt').read_text()
a=raw.index('/-- [aspis_core::field::wide_exact::');b=raw.index('/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::to_le_bytes]: loop body')
body=raw[a:b];names=re.findall(r'(?m)^def\s+([\w.]+)',body);assert len(names)==5,names
assert not any(z in body for z in ['IntoIter','ChunksExactMut','axiom ','sorry','admit','native_decide'])
s='import R1Z.ProverRwFullFuns\nset_option autoImplicit false\nnamespace PDict_CodecSource\nopen Aeneas Aeneas.Std Result ProverRwFull\n'+body+'\n'+''.join(f'\n#print axioms {n}' for n in names)+'\nend PDict_CodecSource\n';p.write_text(s)
(e/'source-cut.json').write_text(json.dumps(dict(selected_definitions=names,emission_sha256=hashlib.sha256(raw.encode()).hexdigest(),module_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification='Exact five complete definitions only. Serializer iterator/chunk templates and serializer loop remain outside accepted closure; no axiom or guessed iterator model selected.'),indent=2)+'\n')
