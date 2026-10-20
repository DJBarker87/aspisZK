from pathlib import Path
import re,json,hashlib,sys
check="--check" in sys.argv
def save(path, content):
 if check:
  assert path.read_text() == content, str(path)
 else: path.write_text(content)
base=Path(__file__).resolve().parents[2]; ev=Path(__file__).resolve().parent
src=base/'evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean'
s=src.read_text()
def extract(name):
 m=re.search(r'(?m)^def(?:\n  | )'+re.escape(name)+r'(?=\s|\n)',s)
 if not m: raise ValueError(name)
 end=s.find('\n/--',m.start())
 return s[m.start():end].strip()+'\n'
names=['verifier.candidate.batch_key_at','verifier.candidate.sort_batch_keys_loop0_loop0.body','verifier.candidate.sort_batch_keys_loop0_loop0','verifier.candidate.sort_batch_keys_loop0.body','verifier.candidate.sort_batch_keys_loop0','verifier.candidate.sort_batch_keys']
body='import R13CloseLoop\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace AspisR1Stage2.R13Close.Sort\n\n'+'\n'.join(extract(n) for n in names)+'\nend AspisR1Stage2.R13Close.Sort\n'
p=base/'lean/R13CloseSortBody.lean';save(p,body)
pins=dict(source=str(src.relative_to(base)),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),modules=[dict(path=str(p.relative_to(base)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),definitions=names,transformation='verbatim definition text under a new namespace; no operations substituted')])


levelNames=['multiproof.Arity.bits','multiproof.verify_in_place_loop0_loop0.body','multiproof.index_at']
level=extract(levelNames[1]).replace('def multiproof.verify_in_place_loop0_loop0.body','def levelBody (ops : LevelOps)').replace('multiproof.verify_in_place_loop0_loop0_loop0 iter', 'ops.eight iter')
level=re.sub(r'    \| multiproof.Arity.Eight =>.*?\n  else ok', '    | multiproof.Arity.Eight => ops.eight idx val at1 w i pending_return parent\n  else ok', level, flags=re.S)
header="""import R13CloseLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close.Level
abbrev Idx := Array U32 16#usize
abbrev Val := Array (Array U8 32#usize) 16#usize
abbrev Out := ControlFlow (multiproof.Arity × Idx × Val × Usize × Usize × Usize × Option Bool) (multiproof.Arity × Idx × Val × Usize × Usize × Option Bool × U32)
structure LevelOps where
  eight : Idx → Val → Usize → Usize → Usize → Option Bool → U32 → Result Out
"""
q=base/'lean/R13CloseLevelBody.lean'
save(q,header+'\n'+extract(levelNames[2])+'\n'+extract(levelNames[0])+'\n'+level+'\nend AspisR1Stage2.R13Close.Level\n')
pins['modules'].append(dict(path=str(q.relative_to(base)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),definitions=levelNames,transformation='new namespace; body renamed levelBody; extra LevelOps argument; entire Eight branch replaced by ops.eight (unreachable in Two proofs); Two branch verbatim'))

scanNames=['verifier.candidate.same_batch_leaf','verifier.candidate.same_batch_index']
scan=extract('verifier.candidate.batch_tree_loop.body')
start=scan.index('    if d > 0#usize')
end=scan.index('\n  else\n    let s1',start)
scan=scan[start:end]
header='''import R13CloseLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close.Dedup
abbrev Idx := Array U32 16#usize
abbrev Val := Array (Array U8 32#usize) 16#usize
abbrev Leaf := Array U8 32#usize
'''
step='''def dedupStep (idx : Idx) (val : Val) (d key_position1 : Usize)
    (index : U32) (leaf : Leaf) :
    Result (ControlFlow (Idx × Val × Usize × Usize)
      (Idx × Val × Option (core.result.Result Unit verifier.Error))) := do
'''+scan+'\n'
r=base/'lean/R13CloseDedupBody.lean'
save(r,header+'\n'+'\n'.join(extract(n) for n in scanNames)+'\n'+step+'\nend AspisR1Stage2.R13Close.Dedup\n')
pins['modules'].append(dict(path=str(r.relative_to(base)),sha256=hashlib.sha256(r.read_bytes()).hexdigest(),definitions=scanNames,subtree_of='verifier.candidate.batch_tree_loop.body',transformation='verbatim dedup subtree after batch_leaf; idx,val,d,key_position1,index,leaf supplied as arguments; new namespace'))


wrapper=extract('multiproof.verify_in_place_loop0_loop0').replace('def multiproof.verify_in_place_loop0_loop0','def levelLoop (ops : LevelOps)').replace('multiproof.verify_in_place_loop0_loop0.body','levelBody ops')
wp=base/'lean/R13CloseLevelRun.lean'
assert wrapper in wp.read_text()
pins['modules'].append(dict(path=str(wp.relative_to(base)),definition_sha256=hashlib.sha256(wrapper.encode()).hexdigest(),definitions=['multiproof.verify_in_place_loop0_loop0'],transformation='wrapper renamed levelLoop; LevelOps parameter added and threaded to levelBody; remaining wrapper verbatim'))
save(ev/'binding.json',json.dumps(pins,indent=2)+'\n')
print('Source bindings: sort definitions, exact dedup subtree, binary body and inner loop wrapper verified.')
