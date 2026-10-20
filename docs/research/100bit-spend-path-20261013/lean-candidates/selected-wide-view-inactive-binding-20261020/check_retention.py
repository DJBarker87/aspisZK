from pathlib import Path
import hashlib,json,subprocess,re
W=Path(__file__).resolve().parent
old='AspisR1SweepV2WideView';new='AspisR1SelectedWideViewV1'
t=(W/'sources/SelectedWideViewTypesV1.lean').read_text();original=(W/'original/Types.lean').read_text()
# Every generated data declaration, including constructor order, is retained.
t=t.split('/-- [aspis_core::field::M31]')[1].split('\ndef transport.Variant.read_discriminant')[0].strip()
original=original.split('/-- [aspis_core::field::M31]')[1].split('\nend '+old)[0].replace('@[discriminant isize]\n','').strip()
assert t==original
# All generated executable bodies are retained; only the two named opaque
# interfaces are instantiated and the enclosing namespace/imports relocated.
marker='/-- [aspis_r1_cost_probe::compact::FINAL_LEN]'
f=(W/'sources/SelectedWideViewFunsV1.lean').read_text().split(marker)[1].split('\n#print axioms')[0]
f=f.replace(new,old).replace('let o ← viewFromBytes s','let o ← aspis_core.field.wide_exact.WideExact.from_le_bytes s').replace('let r ← viewOptionOkOr o verifier.Error.Parse','let r ← core.option.Option.ok_or o verifier.Error.Parse')
assert f.strip()==(W/'original/Funs.lean').read_text().split(marker)[1].strip()
print('PASS: all selected generated data/function bodies retained modulo listed namespace and two interface substitutions; discriminant adapter explicit')
meta=W/'extraction-provenance/candidate-source-reuse.json'
if meta.is_file():
 R=next(x for x in W.parents if (x/'.git').exists())
 pin=json.loads(meta.read_text());raw=subprocess.check_output(['git','show',pin['revision']+':'+pin['path']],cwd=R)
 assert hashlib.sha256(raw).hexdigest()==pin['sha256']
 oldpin=json.loads((W/'extraction-provenance/aeneas-input.json').read_text())
 assert oldpin['source_hashes'][pin['path']]==pin['sha256']
 print('PASS: entire parked candidate source file matches retained extraction input; adoption is not claimed')
