from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028';rows=[]
def body(path,start):
 s=(R/path).read_text();a=s.index(start);j=s.index('{',a)+1;depth=1
 while depth:
  depth+=(s[j]=='{')-(s[j]=='}');j+=1
 b=s[a:j];assert '#[cfg' not in b and 'cfg!' not in b
 rows.append(dict(path=path,start=start,sha256=hashlib.sha256(b.encode()).hexdigest()));return b
core='crates/aspis-core/src/r0_transcript.rs';host='crates/aspis-r1-cost-probe/src/host_transcript.rs';trans='crates/aspis-core/src/transcript.rs'
parts=['#![allow(dead_code)]', 'const QUERY_COUNT:usize=22;const QUERY_MAX_DRAWS:usize=64;const QUERY_BOUND:u32=1<<18;', '#[derive(Debug,PartialEq,Eq)]\n'+body(trans,'pub enum QuerySampleError {'),'type Rank=[u32;8];',body(core,'fn block_rank('),body(core,'fn query_words('),'#[derive(Default)]\n'+body(core,'struct QueryScan {'),body(core,'impl QueryScan {'),body(core,'pub fn queries_from_pairs(')]
parts+=['mod verifier {#[derive(Debug,PartialEq,Eq)] pub enum Error {Transcript}}','mod host {',body(host,'fn queries_from_pairs(').replace('fn queries_from_pairs','pub fn queries_from_pairs',1),body(host,'fn scan_query_words('),body(host,'fn query_contains('),'}']
parts += [r'''
fn reference(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),verifier::Error> {
 let mut accepted=Vec::new();let mut draws=0;
 while draws<64 && accepted.len()<22 {
  let k=draws/8;let j=4*(draws%8);
  let x=u32::from_le_bytes([blocks[k][j],blocks[k][j+1],blocks[k][j+2],blocks[k][j+3]])&0x3ffff;
  draws+=1;
  if !accepted.iter().any(|&v|v==x){accepted.push(x);}
 }
 if accepted.len()!=22 {return Err(verifier::Error::Transcript);}
 let selected=(draws/8).min(7);
 Ok((accepted.try_into().unwrap(),advances[selected]))
}
fn pack(words:&[u32;64])->[[u8;32];8] {
 std::array::from_fn(|k|std::array::from_fn(|j|words[k*8+j/4].to_le_bytes()[j%4]))
}
fn check(words:&[u32;64])->usize {
 let b=pack(words);let a=std::array::from_fn(|i|[i as u8;32]);
 let original=queries_from_pairs(&b,&a).map_err(|_|verifier::Error::Transcript);
 let rewritten=host::queries_from_pairs(&b,&a);let expected=reference(&b,&a);
 assert_eq!(original,expected);assert_eq!(rewritten,expected);1
}
fn main(){
 if std::env::args().any(|x|x=="negative") {
  let w=std::array::from_fn(|i|if i<3 {0}else{(i-2).min(21) as u32});let b=pack(&w);let a=std::array::from_fn(|i|[i as u8;32]);
  assert_eq!(host::queries_from_pairs(&b,&a).unwrap().1,[2;32],"false control: stop-at-draw24 selects advance3");return;
 }
 let mut checks=0;checks+=check(&[0;64]);checks+=check(&[u32::MAX;64]);
 for end in 22..=64 {
  let w=std::array::from_fn(|i|if i<end-21 {0}else{((i-(end-22)).min(21)) as u32});
  checks+=check(&w);
  let a=std::array::from_fn(|i|[i as u8;32]);
  assert_eq!(host::queries_from_pairs(&pack(&w),&a).unwrap().1,[(end/8).min(7) as u8;32]);
 }
 let mut state=0x1531_8765_1234_9abcu64;
 for case in 0..20000 {
  let mask=if case%3==0 {31}else{0x3ffff};
  let w=std::array::from_fn(|_|{state^=state<<13;state^=state>>7;state^=state<<17;(state as u32)&mask});
  checks+=check(&w);
 }
 let status=std::process::Command::new(std::env::current_exe().unwrap()).arg("negative").status().unwrap();assert_eq!(status.code(),Some(101));
 println!("{{\"complete_result_checks\":{},\"directed_stop_positions\":43,\"matched_negative_exit\":101,\"failed\":0}}",checks);
}
''']
b='\n\n'.join(parts)+'\n';(R/'tools/pv-l2d-20261028/query-native-v2.rs').write_text(b)
(E/'query-native-v2-freeze.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),bodies=rows,harness_sha256=hashlib.sha256(b.encode()).hexdigest(),differences=['host queries_from_pairs visibility made pub for test call only','host Error only models the sole produced Transcript variant','core QuerySampleError mapped to Transcript as the actual caller does','no Transcript wrapper or digest invocation is replaced by this gate'],features='selected function bodies contain no cfg/cfg!; client release features in deployed-client-features.json',evidence_class='finite native validation, complete Result and selected-advance bytes; not universal trace equality',remaining=['full branch/read trace association','eager prefetch/native wrapper failed-state law','same endpoint coupling']),indent=2)+'\n')
