#!/usr/bin/env python3
"""Pin and extract shipped loop bodies; map and pure callees are harness substitutes."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent
source=Path('crates/aspis-r1-cost-probe/src/sim.rs')
s=source.read_text();spans=[]
def take(start,end):
 a=s.index(start,s.index('// 6. Commitment programming and serialisation.'));b=s.index(end,a)
 body=s[a:b];spans.append(dict(start_line=s[:a].count('\n')+1,end_line=s[:b].count('\n')+1,sha256=hashlib.sha256(body.encode()).hexdigest()))
 return body
folded=take('        for &u in &drawn.queries { let v=', '        let mut leaves1=')
leaves=take('        for (&u,(_,c1v,c2v)) in &opened', '        let (p1,r1)=')
publish=take('        for &u in &drawn.queries {\n            let u=u as usize;let (_,c1v,c2v)=', '        if out.len()!=compact::OFF_NODES')
merge=take('        for (a,v) in transcript {', '        times.program=')
output='fn native_folded(drawn:&Drawn,view:&View,mut folded:BTreeMap<usize,Vec<u8>>)->BTreeMap<usize,Vec<u8>> {\n'+folded+'folded}\n'
output+='fn native_leaves(opened:&BTreeMap<usize,(u8,Vec<u8>,Vec<u8>)>,folded:&BTreeMap<usize,Vec<u8>>,commit_coins:&mut Coins)->(BTreeMap<usize,(Vec<u8>,[u8;32])>,BTreeMap<usize,(Vec<u8>,[u8;32])>,BTreeMap<usize,(Vec<u8>,[u8;32])>) {let mut leaves1=BTreeMap::new();let mut leaves2=BTreeMap::new();let mut leavesf=BTreeMap::new();\n'
# Native loops take &opened and &folded; wrapper owns snapshots to preserve spans verbatim.
output=output.replace(' {let mut leaves1=', ' {let opened=opened.clone();let folded=folded.clone();let mut leaves1=')
output+=leaves+'(leaves1,leaves2,leavesf)}\n'
output+='fn native_publish(drawn:&Drawn,opened:&BTreeMap<usize,(u8,Vec<u8>,Vec<u8>)>,leaves1:&BTreeMap<usize,(Vec<u8>,[u8;32])>,leaves2:&BTreeMap<usize,(Vec<u8>,[u8;32])>,folded:&BTreeMap<usize,Vec<u8>>,leavesf:&BTreeMap<usize,(Vec<u8>,[u8;32])>)->Vec<u8> {let mut out=Vec::new();\n'+publish+'out}\n'
output+='fn native_merge(mut table:Table,transcript:Table)->Result<Table,Error> {\n'+merge+'Ok(table)}\n'
(H/'native-loops.rs').write_text(output)
(H/'source-spans.json').write_text(json.dumps(dict(source=str(source),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),spans=spans,generated_sha256=hashlib.sha256(output.encode()).hexdigest()),indent=2)+'\n')
