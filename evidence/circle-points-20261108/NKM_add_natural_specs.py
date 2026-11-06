from pathlib import Path
import json,base64,hashlib
E=Path(__file__).resolve().parent;p=E/'NKM_CONTRACT_OVERLAY.json';x=json.loads(p.read_text());n='crates/aspis-r1-cost-probe/src/NKM_native.rs';row=x[n];s=base64.b64decode(row['data']).decode()
s=s.replace('l.events[l.len]=Event{kind,a,b,out};', '''match kind {
 0|4=>kani::assume(out==ns_product(a,b)),
 1=>kani::assume(out==ns_plus(a,b)),
 2=>{if l.inverse_some{kani::assume(a!=QM31::ZERO);kani::assume(ns_product(a,out)==QM31::ONE)}else{kani::assume(a==QM31::ZERO)}},
 3=>kani::assume(out==ns_minus(a,b)),
 _=>unreachable!()
 }
 l.events[l.len]=Event{kind,a,b,out};''')
s+='\n'+(E/'NKM_natural_specs.rs.txt').read_text()
row['before']=row['sha256'];row['data']=base64.b64encode(s.encode()).decode();row['sha256']=hashlib.sha256(s.encode()).hexdigest();p.write_text(json.dumps(x))
p=E/'NKM_SOURCE_PINS.json';pins=json.loads(p.read_text());pins[n]=row['sha256'];p.write_text(json.dumps(pins,indent=2)+'\n')
# Add this overlay delta separately: immutable original contracts and their receipts remain pinned.
(E/'NKM_NATURAL_OVERLAY.json').write_text(json.dumps(dict(path=n,**row)))
for i,old in enumerate([17,18,19,20,21,22],25):
 a=f'NKM_K{i:03}';x=json.loads((E/f'NKM_K{old:03}.json').read_text());x['attempt']=a;x['command'][2]=a+'.json';x['collect']=[n.replace(f'NKM_K{old:03}',a)for n in x['collect']];x['matched_attempt']=f'NKM_K{i-1 if i%2==0 else i+1:03}';x['expected_time']='Optimized native contract with natural-number field oracle assumptions; no field arithmetic law is asserted in Kani';(E/(a+'.json')).write_text(json.dumps(x))
