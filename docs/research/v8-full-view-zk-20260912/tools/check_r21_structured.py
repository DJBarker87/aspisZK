#!/usr/bin/env python3
"""Regenerate exact algebra/wiring evidence and optionally all staged sources."""
import argparse,ast,hashlib,json,subprocess,sys,tempfile
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path);p.add_argument('--output',type=Path)
a=p.parse_args();root=Path(__file__).resolve().parent.parent;tools=root/'tools';evidence=root/'evidence';saved=evidence/'r21-structured-e'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def run(script,*args):subprocess.run([sys.executable,str(tools/script),*map(str,args)],check=True,stdout=subprocess.DEVNULL)
for n,h in read(saved/'MANIFEST.json').items():assert sha(saved/n)==h,n
hashes={}
for n in ['generate_r21_wiring.py','rebalance_r21_dag.py','install_r21_structured.py','r21_wiring.rs','collect_r21_structured.py','check_r21_structured.py']:
    path=tools/n
    if path.suffix=='.py':ast.parse(path.read_text())
    hashes[n]=sha(path)
with tempfile.TemporaryDirectory(prefix='aspis-r21-structured-check-') as temp:
    work=Path(temp);dag=work/'dag';circuit=work/'circuit';wiring=work/'wiring'
    run('rebalance_r21_dag.py','--dag',evidence/'r21-source-a/source-dag.json','--output',dag)
    for n in ['source-dag.json','reassociation.json']:assert (dag/n).read_bytes()==(evidence/'r21-balanced-dag-d'/n).read_bytes(),n
    run('generate_r21_layers.py','--dag',dag/'source-dag.json','--output',circuit)
    for n in ['r21_circuit.rs','circuit.json','circuit-profile.json']:assert (circuit/n).read_bytes()==(evidence/'r21-balanced-circuit-d'/n).read_bytes(),n
    run('generate_r21_wiring.py','--circuit',circuit/'circuit.json','--output',wiring)
    for n in ['r21_wiring_tables.rs','wiring.json']:assert (wiring/n).read_bytes()==(evidence/'r21-wiring-d'/n).read_bytes(),n
    run('rebalance_r21_dag.py','--pairwise','--dag',evidence/'r21-source-a/source-dag.json','--output',work/'pairwise')
    for n in ['source-dag.json','reassociation.json']:assert (work/'pairwise'/n).read_bytes()==(evidence/'r21-balanced-dag-c'/n).read_bytes(),n
    if a.control:
        stage=work/'stage'
        run('stage_r21_pilot.py','--stage',a.control,'--output',stage)
        run('install_r21_circuit.py','--stage',stage,'--circuit',circuit)
        run('install_r21_structured.py','--stage',stage,'--circuit',circuit,'--wiring',wiring)
        expected=read(saved/'r18-stage.json')['files'];actual=read(stage/'r18-stage.json')['files']
        assert actual==expected
        for name,value in expected.items():assert sha(stage/name)==value,name
        pins=len(expected)
    else:pins=None
for w in range(2):
    meta=read(saved/f'svm-world{w}/metadata.json');wire=saved/f'host-world{w}/generated/helper.bin'
    assert sha(wire)==meta['wire_sha256']
    assert wire.read_bytes()[:384]==(evidence/f'r21-source-a/public-world{w}.bin').read_bytes()
report={'integrity':'PASS','generators':'byte-identical with exact algebra/support checks',
        'assembled_source_pins_reproduced':pins,'tool_sha256':hashes,
        'performance_gate':'FAIL (retained honestly)','source_refinement_proved':False,'security_theorem':False}
if a.output:
    assert not a.output.exists();a.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
