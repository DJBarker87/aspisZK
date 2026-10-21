#!/usr/bin/env python3
"""Dependency-sliced validator with the unchanged pure root helper projected."""
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent
import subprocess,sys
raw=subprocess.check_output(['ssh','dombarker@100.108.41.90',
  'cat /home/dombarker/project-offloads/codex-cx-builder-ref9-20261021/drop-opaque-validator/generated/Admission-renamed.lean'],text=True)
assert hashlib.sha256(raw.encode()).hexdigest() == '63c3044dbe71069d760fef6ff9006a8bd887f815b2301bae1e689fe4ece2b754'
def output(p,s):
 if '--check' in sys.argv: assert p.read_text()==s, p
 else: p.write_text(s)
def decl(name):
 m=re.search(r'^(?:def|impl_def|structure|inductive)\s+'+re.escape(name)+r'(?=\s|:|\{|\()',raw,re.M)
 assert m,name
 end=raw.find('/--',m.end())
 return raw[m.start():end].strip()+'\n\n'
names=['aspis_core.field.M31','aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq','aspis_core.field.M31.Insts.CoreCmpPartialEqM31','pool_v1.incremental_merkle.IncrementalMerkleTreeV1','pool_v1.incremental_merkle.PoolV1TreeError','pool_v1.format.POOL_V1_TREE_DEPTH','pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY','pool_v1.incremental_merkle.tree_reference.validate_owned_loop','pool_v1.incremental_merkle.tree_reference.validate_owned']
body=''.join(decl(n) for n in names)
body=body.replace('Std.U64.wrapping_shr i level','R1Z.BuilderStdModels.shift64 i level')
body=body.replace('1#u64 <<< pool_v1.format.POOL_V1_TREE_DEPTH','1#u64 <<< 20#u32')
# Match env J's trait binder requirements: this is just the generated M31 instance.
# Preserve impl_def: ne's default implementation refers to its own trait.
old='''def pool_v1.incremental_merkle.tree_reference.validate_owned
  (tree'''
new='''def pool_v1.incremental_merkle.tree_reference.validate_owned
  (reconstruct : pool_v1.incremental_merkle.IncrementalMerkleTreeV1 →
    Array (Array aspis_core.field.M31 8#usize) 21#usize →
    Result (core.result.Result (Array aspis_core.field.M31 8#usize)
      pool_v1.incremental_merkle.PoolV1TreeError))
  (tree'''
assert body.count(old)==1
body=body.replace(old,new).replace('pool_v1.incremental_merkle.IncrementalMerkleTreeV1.reconstruct_nonfull_root\n              tree empty','reconstruct tree empty')
# Empty docs are omitted; mark only the transparent M31 alias and constants as in raw.
body=body.replace('def aspis_core.field.M31 :=','@[reducible]\ndef aspis_core.field.M31 :=')
s='''-- Dependency slice of the part-9 generated validator; see the port receipt.
import R1Z.BuilderForestStdPort
import R1Z.BuilderStdShift
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace AspisBuilderForestValidator
'''+body+'''
#print axioms pool_v1.incremental_merkle.tree_reference.validate_owned_loop
#print axioms pool_v1.incremental_merkle.tree_reference.validate_owned
end AspisBuilderForestValidator
'''
assert not re.search(r'^axiom\s',s,re.M)
p=H.parent/'lean/R1Z/BuilderForestValidatorExtracted.lean';output(p,s)
(H/'builder-cont10-validator-port.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),adapted_sha256=hashlib.sha256(s.encode()).hexdigest(),selected_declarations=names,root_projection=dict(before='IncrementalMerkleTreeV1.reconstruct_nonfull_root tree empty',after='reconstruct tree empty',status='Explicit arbitrary pure helper parameter; no helper correctness assumed'),changes=['dependency slice only','env-J U64 shift adapter','literal depth shift-count port'],previous_failed_aggregate='J9383: callback borrow-back ABI differs between raw Aeneas output and env-J FnMut state-pair ABI; unrelated callbacks removed by dependency slicing, no failed object accepted',status='Projected validator reference only, not whole forest admission'),indent=2)+'\n')
