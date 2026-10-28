"""Exact frozen associations; syntax evidence, never a whole-execution theorem."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
checks=[]
def check(path,needle,reason):
 b=subprocess.check_output(['git','show',rev+':'+path]);s=b.decode();assert needle in s,(path,needle)
 checks.append(dict(path=path,source_revision=rev,file_sha256=hashlib.sha256(b).hexdigest(),source_fragment=needle,claim=reason))
check('crates/aspis-r1-cost-probe/src/compact.rs','at += 32 * SLOT_NODES[i];\n        i += 1;','Native one-step helper keeps the exact two update expressions; model invariants supply i<6 and at=slotStart(i).')
check('crates/aspis-core/src/r0/merkle.rs','hash.digest(&[\n        &[0x18],\n        &children[0],\n        &children[1],\n        &children[2],\n        &children[3],\n        &children[4],\n        &children[5],\n        &children[6],\n        &children[7],\n    ])','Nine exact source slices, same backend call and returned digest; no SHA value assertion.')
check('crates/aspis-core/src/state_only_private_merkle.rs','hash.digest(&[&[DOM_LEAF, tree_tag], value, salt])','Three exact source slices; prefix domain 0x10; native probe checks lengths/pointer identities/reply coordinate.')
for name,slot in [('is_immutable',26),('is_paused',25)]:
 check('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','registry.'+name+'()',f'V1/V2 typed source branch calls {name}; AdapterRw slots {slot}/{slot+2}; callsite carrier association retained in NDH registry slot theorem.')
model_path='docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean'
model=subprocess.check_output(['git','show','HEAD:'+model_path]);m=model.decode()
for first,second in [(26,25),(28,27)]:
 needle=f'ops.op{first}'
 start=m.index(needle,m.index('def r1_pool_adapter.owned.authenticate_invariant_release_registry'))
 end=m.index(f'ops.op{second}',start)
 assert 'if b' in m[start:end] and 'then' in m[start:end]
 checks.append(dict(path=model_path,sha256=hashlib.sha256(model).hexdigest(),first_immutable_slot=first,second_paused_slot=second,fragment=m[start:end+len(f'ops.op{second}')],claim='Exact coherent source branch order, matching native !immutable || paused rejection; corrected NDH install and NDH_RegistryTail theorem.'))
(E/'NDH_SOURCE_ASSOCIATION.json').write_text(json.dumps(dict(checks=checks,limits='Syntax/pin checks only. Each semantic claim still needs its native and Lean gates.'),indent=2)+'\n')
print('source associations',len(checks))
