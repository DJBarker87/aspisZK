from pathlib import Path
import json,hashlib,subprocess,os
E=Path(__file__).resolve().parent;x=json.loads((E/'NGH_NATIVE_INPUTS.json').read_text())
n='crates/aspis-core/src/NGH_reference.rs'
x[n]=x[n].replace('fn actual_for_contract(){qm31_accumulate_product_channels(kani::any(),QM31::ZERO,QM31::ZERO);}', '''fn actual_for_contract(){
 let q=||QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}};
 qm31_accumulate_product_channels(kani::any(),q(),q());}''')
original=x['crates/aspis-core/src/field.rs']
for k,variant in [(23,'outer_only'),(24,'inner_only')]:
 s=original
 if variant=='outer_only':s=s.replace('        #[cfg_attr(NGH_for_diagnostic,kani::loop_invariant(true))]\n','')
 else:s=s.replace('    #[cfg_attr(NGH_for_diagnostic,kani::loop_invariant(true))]\n    for component','    for component')
 x['crates/aspis-core/src/field.rs']=s
 (E/'NGH_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');(E/'NGH_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()},indent=1)+'\n')
 a=f'NGH_K{k:03}'
 r=subprocess.run(['python3',str(E/'NGH_run.py'),a,'kani','field::NGH_reference::actual_for_contract'],env=dict(os.environ,NGH_CORE='1',NGH_FOR='1',NGH_CODEGEN='1'),capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise RuntimeError(r.stdout+r.stderr)
 receipt=json.loads(p.read_text());print(a,variant,receipt['exit_status'],receipt['wall_seconds'],flush=True)
