#!/usr/bin/env python3
"""Exact source steps, independently checked against indexed references.
No shipped source mutation. The step splice is checked before any host run.
"""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[2]
out=Path(sys.argv[1]);(out/'src').mkdir(parents=True,exist_ok=True)
wide=ROOT/'crates/aspis-r1-cost-probe/src/sampler.rs'
scan=ROOT/'crates/aspis-core/src/r0_transcript.rs'
w=wide.read_text();s=scan.read_text()
def item(s,marker):
 a=s.index(marker);b=s.index('{',a);d=1;e=b+1
 while d:
  d+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
def canon(s):return ''.join(s.split())
div='''let dividend = (remainder << 32) | u64::from(*limb);
*limb = (dividend / u64::from(P)) as u32;
remainder = dividend % u64::from(P);'''
add='''let sum = u64::from(*digit) + u64::from(addend);
*digit = (sum % u64::from(P)) as u32;
addend = (sum / u64::from(P)) as u32;'''
step='''if self.accepted_len == QUERY_COUNT || self.draws == QUERY_MAX_DRAWS {
return true;
}
self.draws += 1;
if !self.accepted[..self.accepted_len].contains(&candidate) {
self.accepted[self.accepted_len] = candidate;
self.accepted_len += 1;
}'''
assert canon('for limb in quotient.iter_mut().rev() {'+div+'}') in canon(item(w,'fn low_base_p_digits('))
assert canon('for digit in digits {'+add+'}') in canon(item(w,'fn add_small_base_p('))
assert canon(item(s,'fn scan('))==canon('fn scan(&mut self, block: &[u8;32])->bool {for candidate in query_words(block) {'+step+'} false}')
# Reference pass is the existing extracted, proved owned-array loop.
pass_body=item(w,'fn qm31_div_pass(')
assert canon(div.replace('*limb','rank[j]')) in canon(pass_body)
code='''#![allow(dead_code)]
const P:u32=2147483647;
const QUERY_COUNT:usize=22;
const QUERY_MAX_DRAWS:usize=64;
#[derive(Clone,Copy)]
'''+item(s,'struct QueryScan {')+'\n'+pass_body+'\n'
code+='fn division_step(mut word:u32, mut remainder:u64)->(u32,u64) {let limb=&mut word;'+div+' (word,remainder)}\n'
code+='fn addition_step(mut word:u32, mut addend:u32)->(u32,u32) {let digit=&mut word;'+add+' (word,addend)}\n'
code+='impl QueryScan {fn step(&mut self,candidate:u32)->bool {'+step+' false}}\n'
code+=item(w,'fn add_small_base_p(')+'\n'+item(w,'fn low_base_p_digits(')+'\n'
code+=(ROOT/'tools/r4-transport2-kit/harness.rs').read_text()
(out/'src/lib.rs').write_text(code)
(out/'Cargo.toml').write_text('[package]\nname="r4-transport2-steps"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
manifest=dict(schema='r4-step-source-splice-v1',sources={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [wide,scan]},crate_sha256=hashlib.sha256(code.encode()).hexdigest(),steps=dict(division=div,addition=add,scan=step),checks=['division body exact in optimized helper and extracted indexed reference','addition body exact in optimized helper','complete scanner body equals eight-word iteration of exact single step'],qualification='Syntactic decomposition plus Kani components. Not a compiler-certified whole-loop extraction equivalence.')
(out/'source-cut.json').write_text(json.dumps(manifest,indent=2)+'\n')
