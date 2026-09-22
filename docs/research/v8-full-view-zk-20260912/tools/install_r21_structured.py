#!/usr/bin/env python3
"""Specialize an isolated R21 pilot, retaining its generic host reference."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True);p.add_argument('--wiring',type=Path,required=True)
p.add_argument('--circuit',type=Path,required=True)
a=p.parse_args();here=Path(__file__).parent;ex=a.stage/'docs/research/v8-no-work-100-20260907/experiments'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((a.stage/'r18-stage.json').read_text());assert 'r21_circuit' in m and 'r21_structured' not in m
for name,h in m['files'].items():assert sha(a.stage/name)==h,name
report=json.loads((a.wiring/'wiring.json').read_text())
assert report['exact_support_equal']
assert sha(a.circuit/'circuit.json')==report['source_circuit_sha256']
assert sha(a.circuit/'r21_circuit.rs')==sha(ex/'r21_circuit.rs')
changed=[]
for name,src in [('r21_wiring.rs',here/'r21_wiring.rs'),('r21_wiring_tables.rs',a.wiring/'r21_wiring_tables.rs')]:
    dest=ex/name;assert not dest.exists();shutil.copy2(src,dest);changed.append(dest)
path=ex/'r21_gkr.rs';text=path.read_text();start=text.index('pub fn verify(');end=text.index('\nfn line_polynomial(',start)
reference=text[start:end].replace('pub fn verify(','pub fn verify_reference(',1)
before='''        let (ez,rest)=scratch.split_at_mut(max_width);let (eu,ev)=rest.split_at_mut(max_width);
        equality_table(&z,ez);equality_table(&u[..k],eu);equality_table(&v[..k],ev);
        let mut left=K::ZERO;let mut right=K::ZERO;let mut product=K::ZERO;
        for (g,&gate) in layer.iter().enumerate() {
            if gate.0==4{continue;}
            let weight=ez[g].mul(eu[gate.1 as usize]).mul(ev[gate.2 as usize]);
            match gate.0 {0=>{left=left.add(weight);right=right.add(weight)},1=>product=product.add(weight),2=>{left=left.add(weight);right=right.sub(weight)},3=>left=left.add(weight),_=>return Err(())}
        }
        if claim!=left.mul(vu).add(right.mul(vv)).add(product.mul(vu).mul(vv)){return Err(());}'''
assert text.count(before)==1
text=text.replace(before,'''        if claim!=r21_wiring::endpoint(level,&z,&u[..k],&v[..k],vu,vv,&mut scratch){return Err(());}''')
anchor='    if c.layers.last().map(|x|x.len())!=Some(1)'
identity=list(bytes.fromhex(m['r21_circuit']['profile']['circuit_id']))
assert text.count(anchor)==1
text=text.replace(anchor,f'    if c.id!={identity}{{return Err(());}}\n'+anchor)
text=text.replace('let mut scratch=vec![K::ZERO;3*max_width];','let mut scratch=vec![K::ZERO;(3*max_width).max(r21_wiring::MAX_NODES)];')
text+='\n#[cfg(not(target_os="solana"))]\n'+reference+'\n'
text+='\n#[path="r21_wiring.rs"] pub mod r21_wiring;\n'
path.write_text(text);changed.append(path)
path=ex/'r21_pilot.rs';text=path.read_text()
text=text.replace('    let mut seed=', '    r21_gkr::r21_wiring::check(&CIRCUIT);\n    let mut seed=',1)
anchor='    assert!(r21_gkr::verify(&CIRCUIT,&context,&input,output,&proof).is_ok());'
assert text.count(anchor)==1
text=text.replace(anchor,anchor+'\n    assert!(r21_gkr::verify_reference(&CIRCUIT,&context,&input,output,&proof).is_ok());')
path.write_text(text);changed.append(path)
for path in changed:m['files'][str(path.relative_to(a.stage))]=sha(path)
m['r21_structured']={'wiring':report,'generic_reference_host_only':True,'full_aspis_verifier':False,'files':{str(p.relative_to(a.stage)):sha(p)for p in changed}}
(a.stage/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(a.stage),'nodes':report['total_nodes'],'source_pins':len(m['files'])}))
