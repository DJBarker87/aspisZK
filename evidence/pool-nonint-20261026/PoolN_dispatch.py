from pathlib import Path
import json,hashlib,re
B=Path(__file__).parent;s=Path('programs/aspis-pool/src/processor.rs').read_text();start=s.index('let result = if ',s.index('pub fn process_instruction('));pos=start+len('let result = ');branches=[]
while s.startswith('if ',pos):
 a=pos+3;o=s.index('{',a);condition=s[a:o].strip();depth=1;j=o+1
 while depth:
  if s[j]=='{':depth+=1
  elif s[j]=='}':depth-=1
  j+=1
 body=s[o+1:j-1];calls=re.findall(r'(process_[a-z0-9_]+)\s*\(',body);assert len(calls)==1,calls
 branches.append({'condition':condition,'handler':calls[0],'start':a,'end':j,'body_sha256':hashlib.sha256(body.encode()).hexdigest()})
 pos=j
 while s[pos].isspace():pos+=1
 assert s.startswith('else ',pos);pos+=5
assert len(branches)==14,len(branches)
rust='\n#[cfg(kani)]\nmod PoolN_dispatch {\nuse super::*;\nfn PoolN_route(data:&[u8])->Result<u8,ProgramError> {\nlet magic=data.get(..4).ok_or(ProgramError::InvalidInstructionData)?;\n'
for i,b in enumerate(branches):rust+=('if ' if i==0 else 'else if ')+b['condition']+' { Ok('+str(i)+') }\n'
rust+='else {Err(ProgramError::InvalidInstructionData)}\n}\n'
magic=[('AS8I',0),('AS8C',1),('AS8D',2),('ASQ8',3),('ASIN',5),('ASDI',6),('ASPP',7),('ASPX',8),('ASPF',9),('ASPT',12),('ASWD',13)]
rust+='''#[kani::proof]
#[kani::unwind(18)]
fn PoolN_dispatch_projection() {
 let data:[u8;4]=kani::any();let result=PoolN_route(&data);
 assert!(!matches!(result,Ok(4|10|11)));
'''
for m,i in magic:
 rust+=f' assert_eq!(PoolN_route(b"{m}"),Ok({i}));\n kani::cover!(PoolN_route(b"{m}")==Ok({i}),"{m} route reachable");\n'
for m in ['ASF8','ASJP','ASJW']:rust+=f' assert_eq!(PoolN_route(b"{m}"),Err(ProgramError::InvalidInstructionData));\n'
condition=' && '.join(f'&data != b"{m}"' for m,i in magic)
rust+=' if '+condition+' {assert_eq!(result,Err(ProgramError::InvalidInstructionData));}\n}\n}\n'
(B/'PoolN_dispatch_harness.rs').write_text(rust)
(B/'PoolN_dispatch-pin.json').write_text(json.dumps({'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'branches':branches,'adaptation':'Exact original branch predicates; each child body projected to numeric branch index. This proves control projection and nonvacuity, not child effects or whole native dispatch equivalence. All 11 selected and3 excluded handlers accounted.'},indent=2)+'\n')
