#!/usr/bin/env python3
"""Apply timers to a disposable pinned source tree, never to shipped worktree files."""
from pathlib import Path
import sys,re,json,hashlib
R=Path(sys.argv[1]).resolve()
assert 'project-offloads/codex-cx-prover-speed-20261022/' in str(R)
before={}
def edit(path,fun):
 p=R/path;s=p.read_text();before.setdefault(path,hashlib.sha256(s.encode()).hexdigest());p.write_text(fun(s))
def guards(path,names):
 def go(s):
  for name,label in names:
   pattern=r'\bfn '+re.escape(name)+r'\b'
   m=re.search(pattern,s);assert m,(path,name)
   at=s.index('{',m.end())+1
   s=s[:at]+'\nlet _speed_guard = crate::speed_prof::span("'+label+'");\n'+s[at:]
  return s
 edit('crates/aspis-r1-cost-probe/src/'+path,go)
def replace(path,a,b):
 def go(s):
  assert s.count(a)==1,(path,a,s.count(a));return s.replace(a,b)
 edit(path,go)
base='crates/aspis-r1-cost-probe/src/'
edit(base+'lib.rs',lambda s:s+'\npub mod speed_prof;\n')
(R/(base+'speed_prof.rs')).write_text('''use std::{cell::RefCell, time::Instant, collections::BTreeMap, vec::Vec};
std::thread_local! {static STATE: RefCell<(Vec<f64>, BTreeMap<&'static str,(f64,f64,u64)>)> = RefCell::new((Vec::new(), BTreeMap::new()));}
pub struct Span { label: &'static str, start: Instant }
pub fn span(label: &'static str)->Span { STATE.with(|s| s.borrow_mut().0.push(0.0)); Span{label,start:Instant::now()} }
impl Drop for Span {fn drop(&mut self){let elapsed=self.start.elapsed().as_secs_f64(); STATE.with(|s|{let mut s=s.borrow_mut(); let child=s.0.pop().unwrap();if let Some(p)=s.0.last_mut(){*p+=elapsed;}let r=s.1.entry(self.label).or_default();r.0+=elapsed;r.1+=elapsed-child;r.2+=1;});}}
pub fn take()->BTreeMap<&'static str,(f64,f64,u64)>{STATE.with(|s|{assert!(s.borrow().0.is_empty()); core::mem::take(&mut s.borrow_mut().1)})}
''')
guards('prover.rs',[('prove_masked_retrying_with','retry_loop'),('prove_masked_attempt','attempt_context'),('prove_masked_with_attempt','mask_apply_audit'),('derive_private_salts','salts'),('prove_from_semantics','opening_sumcheck_other'),('public_check','p_r1'),('c1','commit_c1'),('c2','commit_c2'),('round','sumcheck_round'),('fold','sumcheck_fold')])
guards('host_semantic.rs',[('build_with_material','semantic'),('no_pole','pole_check')])
guards('host_sumcheck.rs',[('build','semantic_sumcheck')] if re.search(r'fn build\b',(R/(base+'host_sumcheck.rs')).read_text()) else [])
guards('host_commitment.rs',[('new','encoding_domain'),('encode','encoding')])
guards('multiproof.rs',[('new','tree_parents')])
guards('transcript.rs',[(n,'transcript') for n in ['new','absorb','block','scalar','scalar_k','queries']])
guards('weights.rs',[('new','weights'),('materialize','weights_materialize')])
# Fine scopes within existing serial blocks. No arithmetic/order changes.
path=base+'prover.rs'
replace(path,'let (reserved,material)=attempt.reserve_and_build_pool_v1_pair_forest_mask_material_v1(hash,binding,context,nonce_store).map_err(mask_error)?;', 'let (reserved,material)={let _g=crate::speed_prof::span("reservation_and_mask_material");attempt.reserve_and_build_pool_v1_pair_forest_mask_material_v1(hash,binding,context,nonce_store).map_err(mask_error)?};')
replace(path,'let attempt=next_attempt(k)?;','let attempt={let _g=crate::speed_prof::span("entropy");next_attempt(k)?};')
replace(path,'let folded_word=backend.domain.evaluate(&q1,0).map_err(|_|Error::Allocation)?;', 'let folded_word={let _g=crate::speed_prof::span("folded_encoding");backend.domain.evaluate(&q1,0).map_err(|_|Error::Allocation)?};')
replace(path,'let mut leaves=Vec::with_capacity(1<<18);','let leaf_guard=crate::speed_prof::span("folded_leaves");\nlet mut leaves=Vec::with_capacity(1<<18);')
replace(path,'let tree=multiproof::BinaryTree::new','drop(leaf_guard);\nlet tree=multiproof::BinaryTree::new')
replace(path,'let mut out=Vec::with_capacity(compact::PROOF_BYTES);','let _publish=crate::speed_prof::span("publication");\nlet mut out=Vec::with_capacity(compact::PROOF_BYTES);')
path=base+'host_commitment.rs'
replace(path,'let mut leaves = filled(FIBRE_COUNT, [0; 32])?;', 'let leaf_guard=crate::speed_prof::span("commit_leaves");\nlet mut leaves = filled(FIBRE_COUNT, [0; 32])?;')
replace(path,'        Ok(Self {\n            time,','        drop(leaf_guard);\n        Ok(Self {\n            time,')
# Keep v2 production TLS gate intact; checker timings are emitted only in scratch checker.
path='docs/research/v8-r0-zk-20261009/z4/z9e.rs'
replace(path,'        let (mut pb, cc) = convert(&p, &cert, &ln)?;\n        extracted_builders(&p, &cert, &ln, &mut pb)?;', '        let (mut pb, cc) = convert(&p, &cert, &ln)?;\n        let convert_seconds=t.elapsed().as_secs_f64();\n        let tb=Instant::now();\n        extracted_builders(&p, &cert, &ln, &mut pb)?;\n        eprintln!("SPEED_CHECK_SPLIT {} {}",convert_seconds,tb.elapsed().as_secs_f64());')
replace(path,'    (matches!(verdict, Ok(Some(true))), tm)','    eprintln!("SPEED_CHECK {} {} {} {}",tm.public_data,tm.emit,tm.builders,tm.check);\n    (matches!(verdict, Ok(Some(true))), tm)')
(R/'instrumentation.json').write_text(json.dumps({p:{'before':h,'after':hashlib.sha256((R/p).read_bytes()).hexdigest()} for p,h in before.items()},indent=2)+'\n')
