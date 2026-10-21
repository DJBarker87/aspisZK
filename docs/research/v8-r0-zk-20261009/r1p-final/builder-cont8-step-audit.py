#!/usr/bin/env python3
"""Check the P6 single-step source slice; never claim a full-loop verdict."""
import pathlib,re,json,hashlib,subprocess
H=pathlib.Path(__file__).resolve().parent;R=H.parents[3]
p=R/'crates/aspis-statement/src/pool_v1/incremental_merkle.rs'
q=R/'tools/r1-builder-reference/tree.rs'
s=p.read_text();r=q.read_text()
guard='while carry_level < POOL_V1_TREE_DEPTH && (leaf_index >> carry_level) & 1 == 1 {'
a=s.index(guard)+len(guard);b=s.index('\n        }',a)
body=s[a:b].strip()
expected=body.replace('&frontier[carry_level]','&frontier_node').replace('frontier[carry_level] = self.empty[carry_level];','let cleared_node=empty_node;')
normalize=lambda x:re.sub(r'\s+','',x)
assert normalize(expected) in normalize(r)
assert 'kani::assume(carry_level<20)' in r
rec=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reference_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),
 actual_guard=guard,actual_step=body,harness_step=expected,
 scope='Value projection of one iteration at every admissible level, arbitrary frontier-node/empty-node/carry words and every output limb. Array index/update and frame laws are Lean obligations, not silently dropped Kani assertions; not a whole append_one Kani verdict.',
 trust_boundary='P6 Kani/CBMC and Rust compiler/source slicing. No Lean axiom or assumed cryptographic property.')
(H/'builder-cont8-step-audit.json').write_text(json.dumps(rec,indent=2)+'\n')
print('Exact shipped carry body matches the step harness')
