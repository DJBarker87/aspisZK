"""Reify the physical source loop body; preserve every pure Result instruction."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2]; L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'Port3_NativeBatchBody.lean').read_text()
a=s.index('  := do\n',s.index('def verifier.candidate.batch_tree_loop.body'))+len('  := do\n')
b=s.index('\n/--',a)
lines=s[a:b].splitlines(); out=[]; i=0; lifts=0; leaves=0; verifies=0
while i<len(lines):
 line=lines[i]; m=re.match(r'( *)(let .*? ←)(.*)',line)
 if m:
  indent=len(m[1]); rhs=[m[3].strip()];i+=1
  while i<len(lines) and (not lines[i].strip() or len(lines[i])-len(lines[i].lstrip())>indent):
   rhs.append(lines[i].strip());i+=1
  expr='\n'.join(rhs).strip()
  if expr.startswith('ops.op6 '):
   assert re.sub(r'\s+',' ',expr)=='ops.op6 aspis_coredigestDigest32Inst hash tree q'
   expr='Port4B_LeafCode.code tree q';leaves+=1
  elif expr.startswith('ops.op10 '):
   assert re.sub(r'\s+',' ',expr)=='ops.op10 aspis_coredigestDigest32Inst hash multiproof.Arity.Two root idx val d s3'
   expr='verify root idx val d s3';verifies+=1
  else:expr='liftResult (\n'+expr+'\n)';lifts+=1
  out.append(m[1]+m[2]+' '+expr.replace('\n','\n'+m[1]+'  '))
 else:out.append(line);i+=1
body=re.sub(r'\bok\b','pure','\n'.join(out))
body=body.replace('multiproof.Arity.','Port3_NativeBatchBody.multiproof.Arity.').replace('verifier.candidate.batch_tree.closure.','Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.')
assert (leaves,verifies)==(1,1)
header='''import Port9OR_P6Verify
import Port4B_Install

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_BatchStep
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2 CheckpointBytes5Effect

universe u
theorem pair_match {A B : Type} {C : Sort u} (x : A × B) (f : A → B → C) :
    (match x with | (a,b) => f a b)=f x.1 x.2 := by cases x;rfl

abbrev Indices := Array U32 16#usize
abbrev Values := Array (Array U8 32#usize) 16#usize
abbrev Next := Indices × Values × Usize × Usize
abbrev Out := Indices × Values × Option (core.result.Result Unit verifier.Error)

def ops (base : Port3_NativeBatchBody.Ops) := Port3_BatchStd.install (Port4B_VerifyInstall.install base)

def verify (root : Digest) (idx : Indices) (val : Values) (n : Usize) (nodes : Slice U8) :
    Code (Bool × Indices × Values) := do
  let (accepted,out) ← Port9OR_P6Verify.code root ⟨idx,val,n,0#usize⟩ nodes
  pure (accepted,out.idx,out.val)

theorem verify_source (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (root : Digest)
    (idx : Indices) (val : Values) (n : Usize) (nodes : Slice U8) :
    erase D hash (verify root idx val n nodes)=
      (ops base).op10 D hash .Two root idx val n nodes := by
  simp only [verify,erase_bind,erase_pure,Port9OR_P6Verify.source]
  rfl

def body (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (root : Digest) (tree : Usize) (hash : Hash)
    (lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Indices) (val : Values) (d key_position : Usize) : Code (ControlFlow Next Out) :=
  let ops := ops base
  let s := slot
  do
'''
footer='''

theorem source (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Indices) (val : Values) (d pos : Usize) :
    erase D hash (body base D proof root tree hash lo n slot keys idx val d pos)=
      Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body (ops base)
        D proof root tree hash lo n slot keys idx val d pos := by
  simp only [body,erase_bind,erase_lift,erase_pure,erase_ite,verify_source base,pair_match]
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  repeat
    first
    | rfl
    | (fail_if_no_progress dsimp only)
    | (fail_if_no_progress simp only [erase_bind,erase_pure,erase_lift,erase_ite,CheckpointBytes5Effect.bind,verify_source base,pair_match])
    | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro value success)
    | casesm (_ × _)
    | casesm (core.ops.control_flow.ControlFlow _ _)
    | (split <;> (try simp_all only [if_true,if_false]))
  all_goals try simp only [erase_bind,erase_pure,erase_lift,verify_source base,pair_match]
  all_goals rfl

#print axioms pair_match
#print axioms verify_source
#print axioms source
end AspisR1.Port9OR_BatchStep
end
'''
# Code's do block is indented two additional spaces; all source expressions retained.
text=header+'\n'.join('  '+line for line in body.splitlines())+footer
p=L/'Port9OR_BatchStep.lean'
if '--check' in sys.argv:assert p.read_text()==text
else:p.write_text(text)
print(dict(pure_lifts=lifts,leaf_calls=leaves,verify_calls=verifies))
