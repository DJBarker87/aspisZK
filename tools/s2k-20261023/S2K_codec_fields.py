from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s2k-20261023';p=E/'S2K-codec/lib.rs';s=p.read_text();assert 'S2K_reference_fields' not in s
cuts=json.loads((E/'result-field-cuts.json').read_text());adapt=[];helpers=[]
params={'magic':('',{}),'version':('',{}),'kind':(', kind: u8',{'result.transition_kind as u8':'kind'}),'digest_version':('',{}),'lane':(', lane: u8',{'result.output_lane':'lane'}),'master':(', master: &[u8;32]',{'&result.master_account':'master'}),'selected':(', selected: &[u8;32]',{'&result.selected_lane_account':'selected'}),'nullifier':(', nullifier: &Digest',{'&result.nullifier':'nullifier'})}
for name,(param,replacements) in params.items():
 body=cuts[name]['cut']
 for old,new in replacements.items():body=body.replace(old,new)
 helpers.append(f'\npub fn S2K_store_{name}(mut output: [u8;792]{param}) -> [u8;792] {{\n    '+body+'\n    output\n}\n')
 adapt.append(dict(field=name,source_cut=cuts[name],parameter_replacements=replacements,body=body))
entry='''
pub fn S2K_reference_fields(master: [u8;32], selected: [u8;32], nullifier: Digest,
    kind: u8, lane: u8, afterstate: [u8;688]) -> [u8;792] {
    let output = [0u8;792];
    let output = S2K_store_magic(output);
    let output = S2K_store_version(output);
    let output = S2K_store_kind(output,kind);
    let output = S2K_store_digest_version(output);
    let output = S2K_store_lane(output,lane);
    let output = S2K_store_master(output,&master);
    let output = S2K_store_selected(output,&selected);
    let output = S2K_store_nullifier(output,&nullifier);
    S2K_store_afterstate(output,&afterstate)
}
'''
p.write_text(s+''.join(helpers)+entry)
(E/'codec-fields-source.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),lib_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),fields=adapt,entry=entry,scope='Source field boundary reference, with immutable result fields explicit. Each store has native write/frame evidence. Not a whole emitter or validation-success substitute.'),indent=2)+'\n')
subprocess.run(['rsync','-az',str(E/'S2K-codec')+'/','dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-s2k-20261023/S2K-codec/'],check=True)
