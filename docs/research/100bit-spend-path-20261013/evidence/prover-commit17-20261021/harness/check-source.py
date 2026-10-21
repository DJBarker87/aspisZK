#!/usr/bin/env python3
"""Bind the small checked cuts to exact source expressions; no semantic theorem.
Run locally with --check; write a manifest only for the pinned snapshot.
"""
import hashlib,json,sys
from pathlib import Path
E=Path(__file__).resolve().parent.parent
p=Path('crates/aspis-r1-cost-probe/src/prover.rs');s=p.read_text()
checks={
 'header':['out.extend_from_slice(compact::MAGIC);','out.extend_from_slice(&[variant.tag(),0,0,0,0,0,0,0]);'],
 'transcript':['compact::compact_semantic(&sem.bytes,&mut out).map_err(|_|Error::Semantic)?;','compact::compact_values(&y1,&mut out).map_err(|_|Error::Semantic)?;'],
 'opening':['for s in 0..4 {for l in (0..26).chain(core::iter::once(28))','&opening.values[s][l].to_le_bytes()[..if l<26 {4}else{16}]','for s in 0..4 {for l in 26..28'],
 'nodes':['for (batch,range) in [(0usize,0..compact::SPLIT),(1,compact::SPLIT..22)]','for t in 0..3','out.extend_from_slice(&nodes);out.resize(out.len()+cap-nodes.len(),0);'],
 'ordered_projection':['queries[range.clone()].iter().map(|&u|if t==2 {u/4} else {u}).collect();','idx.sort();idx.dedup();'],
}
for phase,expressions in checks.items():
 for expr in expressions:assert expr in s,(phase,expr)
assert p.read_bytes()==(E/'rust-sources/prover.rs').read_bytes()
assert Path('crates/aspis-r1-cost-probe/src/compact.rs').read_bytes()==(E/'rust-sources/compact.rs').read_bytes()
assert (E/'rust-sources/compact-with-harness.rs').read_bytes()==(E/'rust-sources/compact.rs').read_bytes()+(E/'rust-sources/serialization17.rs').read_bytes()
manifest=dict(source_revision='47ccfa22c',source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),cuts=checks,
 scope='Verbatim expression/source binding only. The four Kani phase checks are bounded emission cuts, not full-section or full-function proofs. Sort/dedup, semantic framing, callbacks and Rust/List transport remain open.')
text=json.dumps(manifest,indent=2)+'\n';q=E/'source-binding.json'
if '--check' in sys.argv:assert q.read_text()==text
else:q.write_text(text)
print('Source expression bindings match; no claim of whole-function equivalence.')
