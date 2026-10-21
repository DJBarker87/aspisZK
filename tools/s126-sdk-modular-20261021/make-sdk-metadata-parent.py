#!/usr/bin/env python3
"""Factor the exact metadata prefix in the complete emitted SDK parent."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
O=Path(sys.argv[1]) if len(sys.argv)>1 else D;O.mkdir(exist_ok=True,parents=True)
s=(D/'S2SdkOwnedModelV1.lean').read_text();a=s.index('def owned_stage1_body (ops : Ops)');b=s.index('\ndef owned_stage1 (ops : Ops)',a);body=s[a:b];body=body[:body.rfind('/--')].rstrip()
pat=r'(?m)^( +)let \(r1, sdk1, guards1\) ←\n\s+owned_acquire_checkpoint sdk guards\n\s+checkpoint.data_slot\n'
spans=[]
for m in re.finditer(pat,body):
 n=len(m[1]);end=m.end()+re.search(r'(?m)^ {0,'+str(n-1)+r'}\S',body[m.end():]).start()
 spans.append((m.start(),end,n,'\n'.join(x[n:] for x in body[m.start():end].rstrip().splitlines())))
assert len(spans)==2
ret='Result ((core.result.Result Unit solana_program_error.ProgramError) × OwnedSdk × LiveGuards)'
head='''-- Exact emitted metadata prefix plus both complete original continuations.
import S2SdkSnapshotEquivalenceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.MetadataParent
'''
continuations=''
for i,(_,_,_,suffix) in enumerate(spans):
 continuations+=f'''def continuation{i} (ops : Ops) (sdk : OwnedSdk) (data : Slice U8)
    (guards : LiveGuards) (proof public1 checkpoint : OwnedAccount) :
    {ret} := do
'''+''.join('  '+line+'\n' for line in suffix.splitlines())+'\n'
for i,(a,b,n,_) in reversed(list(enumerate(spans))):body=body[:a]+' '*n+f'next{i} proof public1 checkpoint\n'+body[b:]
body=body.replace('def owned_stage1_body (ops : Ops)',f'def metadataWith (next0 next1 : OwnedAccount → OwnedAccount → OwnedAccount → {ret}) (ops : Ops)',1)
tail='''
/-- All-outcome equality in the complete reference body. Both admitted
instruction branches, every rejection and every original continuation remain.
This fission adds no metadata/callee-success or guard-release premise. -/
theorem body_factor (ops : Ops) (program : Array U8 32#usize)
    (sdk : OwnedSdk) (data : Slice U8) (guards : LiveGuards) :
    owned_stage1_body ops program sdk data guards =
      metadataWith (continuation0 ops sdk data guards)
        (continuation1 ops sdk data guards) ops program sdk data guards := by
  snapshot_defeq

def stage1 (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : alloc.vec.Vec U8) :
    Result ((core.result.Result Unit solana_program_error.ProgramError) × OwnedSdk) := do
  let guards : LiveGuards := {checkpoint:=none,«public»:=none,proof:=none}
  let (status,heap,live) ← metadataWith
    (continuation0 ops sdk (alloc.vec.Vec.deref data) guards)
    (continuation1 ops sdk (alloc.vec.Vec.deref data) guards)
    ops program sdk (alloc.vec.Vec.deref data) guards
  let finalHeap ← owned_release_guards heap live
  ok (status,finalHeap)

/-- Fission is installed through the complete stage1, including cleanup. -/
theorem stage1_eq (ops : Ops) (program : Array U8 32#usize) (sdk : OwnedSdk)
    (data : alloc.vec.Vec U8) : stage1 ops program sdk data=owned_stage1 ops program sdk data := by
  snapshot_defeq

#print axioms body_factor
#print axioms stage1_eq
end AspisS2OwnedStage1.SdkReference.MetadataParent
'''
(O/'S2SdkMetadataParentV1.lean').write_text(head+continuations+body+'\n'+tail)
