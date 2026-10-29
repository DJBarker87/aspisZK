from pathlib import Path
import subprocess,re,json,hashlib,shlex
read=lambda p:subprocess.check_output(['git','show','HEAD:'+p],text=True)
def literals(s):
 cs={n:[int(v) for v in re.findall(r'(\d+)#u8',xs)] for n,xs in re.findall(r'def (c\d+) : List U8 := \[([^]]*)\]',s)}
 for n,c,v in re.findall(r'def (c\d+) : List U8 := List.replicate (\d+) (\d+)#u8',s):cs[n]=[int(v)]*int(c)
 names=re.findall(r'c\d+',re.search(r'def bytes : List U8 := ([^\n]+)',s)[1]);assert len(names)==len(cs)
 return sum([cs[n] for n in names],[])
s=read('evidence/pv-2tnv-20261028/resume/JFx_DataPublic00.lean.txt');b=literals(s);assert len(b)==1880
rq=read('evidence/pv-2tnv-20261028/resume/JHb_DataRequest.lean.txt');q=literals(rq);assert b[1664:]==q[104:]
expected=[0]+b[1744:1776]+b[1776:1808]+b[1808:1812]+[1]+b[1816:1848]+b[1848:1880]+[0]+b[296:304]+b[336:976]+b[992:1024]+b[1024:1664]
assert len(expected)==1455
src='''use aspis_statement::pool_v1::*;
const PUBLIC:&[u8]=&PUBLIC_LITERAL;
const EXPECTED:&[u8]=&EXPECTED_LITERAL;
fn main(){
 let statement=decode_pool_v1_pair_forest_terminal_statement_v1(PUBLIC).unwrap();
 let actual=statement.semantic_public().public_bytes().unwrap();
 assert_eq!(actual.as_slice(),EXPECTED);
 assert_eq!(statement.common().lane_transition.live_snapshot.next_pair_index,13);
 let mut bad=EXPECTED.to_vec();bad[135]=0;assert_ne!(actual,bad);
 println!("{{\\"fixture\\":\\"transfer-13\\",\\"semantic_bytes\\":1455,\\"all_fields\\":true,\\"negative_control\\":true,\\"pass\\":true}}");
}
'''.replace('PUBLIC_LITERAL',str(b)).replace('EXPECTED_LITERAL',str(expected))
p=Path('tools/pv-rj4idb-20261029/statement.rs');p.write_text(src)
E=Path('evidence/pv-rj4idb-20261029');(E/'statement-native-inputs.json').write_text(json.dumps(dict(public_source_sha256=hashlib.sha256(s.encode()).hexdigest(),request_source_sha256=hashlib.sha256(rq.encode()).hexdigest(),public_bytes_sha256=hashlib.sha256(bytes(b)).hexdigest(),expected_semantic_bytes_sha256=hashlib.sha256(bytes(expected)).hexdigest(),extraction='parse literal cNN arrays/replicates in exact def bytes order; exact 216-byte request/payment equality; explicit public_bytes source offsets',classification='finite fixed-fixture validation; not an actual live-plan identification',compiler='deployed rustc1.94.1 profile and rlibs'),indent=2)+'\n')
H='/home/dombarker/project-offloads/codex-pv-rj4idb-20261029';code='import pathlib,sys;pathlib.Path('+repr(H+'/statement.rs')+').write_text(sys.stdin.read())'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=src,text=True,capture_output=True);assert r.returncode==0,r.stderr
print('statement finite test staged; 1880 public bytes -> 1455 semantic bytes')
