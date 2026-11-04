from pathlib import Path
import subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent
for n in ['NEP_Driver','NEP_WALKER','NEP_Planted','NEP_Mutations']:
 b=subprocess.check_output(['git','show','research:evidence/axaudit2-20261102/'+n+'.lean'])
 p=E/('inputs/'+n+'.lean');p.parent.mkdir(exist_ok=True);p.write_bytes(b)
 if n!='NEP_Driver':(E/(n+'.lean')).write_bytes(b)
s=(E/'inputs/NEP_Driver.lean').read_text();roots=json.loads((E.parent/'pv-evhc8-20261104/RAW-ROOTS.json').read_text())
old='(#[`RPx_Deployed, `NDR_CombinedAudit],\n     #[`AspisR1.RPx_Deployed.deployed, `AspisR1.NDR_CombinedAudit.sourceOnHeadline])'
new='(#[`PV_BR_FixtureConsumer, `RPx_Deployed, `NDR_CombinedAudit],\n     #['+',\n       '.join('`'+r for r in roots)+'])'
assert old in s;s=s.replace(old,new)
s=s.replace('(#[`NEP_Planted, `NEP_Mutations],','(#[`NEP_Planted, `NEP_Mutations, `PV_D595_Cases],')
s=s.replace('`NEP_MutateProof.proof, `NEP_MutateAux.viaAux])','`NEP_MutateProof.proof, `NEP_MutateAux.viaAux,\n       `PV_D595_Cases.payload, `PV_D595_Cases.proof])')
s=s.replace('(#[`JGx_SdkAfterValidationEq], #[`AspisR1.JGx_SdkAfterValidationEq.source])','(#[`NEP_Planted], #[`PV_D595_Cases.deliberatelyMissing])')
(E/'NEP_Driver.lean').write_text(s)
(E/'DRIVER.diff').write_text(''.join(difflib.unified_diff((E/'inputs/NEP_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='research:NEP_Driver.lean',tofile='D595:NEP_Driver.lean')))
(E/'PV_D595_Cases.lean').write_text('''module
public import NEP_Planted
noncomputable section
namespace PV_D595_Cases
public inductive Box where
  | mk : Nat → Box
private def secret : Nat := NEP_Planted.auxAx
public def payload : Box := Box.mk secret
public theorem proof : True := NEP_Planted.proof
end PV_D595_Cases
#print axioms PV_D595_Cases.payload
#print axioms PV_D595_Cases.proof
''')
# Only name lists may differ: strip the module/root choice block and compare all other bytes.
def strip(t):
 a=t.index('  let (modules, roots) :=');b=t.index('  let env ←',a)
 return t[:a]+t[b:]
assert strip(s)==strip((E/'inputs/NEP_Driver.lean').read_text())
(E/'DRIVER-FORM.json').write_text(json.dumps(dict(form='adapted copy: only imported module names and root names differ',reason='Original main accepts only final/fixtures/small selectors; no module/root arguments. An import-only wrapper cannot replace those fixed lists.',walker='NEP_WALKER.lean byte-identical to research',diff='DRIVER.diff',non_name_code_identical=True),indent=2)+'\n')
for n in ['lakefile.toml','lake-manifest.json','lean-toolchain']:(E/n).write_bytes((E.parent/'pv-evhc8-20261104'/n).read_bytes())
