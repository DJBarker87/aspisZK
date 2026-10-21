#!/usr/bin/env python3
"""Preserve emitted any control flow with explicit pointer types and next.
No pointer representation or implementation is selected by this adapter.
"""
from pathlib import Path
import re,sys,json,hashlib
I=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(exist_ok=True,parents=True)
raw=(I/'Funs.lean').read_text()
rawTypes=(I/'Types.lean').read_text()
assert 'def checkpoint_nonzero.closure := Unit' in rawTypes
a=raw.index('/-- [core::slice::iter::');z=raw.index('\nend AspisS2StdAny',a)
s=raw[a:z]
s=re.sub(r'@\[.*?\]\n','',s,flags=re.S)
sourceNames=['core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any_loop.body','core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any_loop','core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any']
for old,new in zip(sourceNames,['anyBody','anyLoop','sourceAny']):s=s.replace(old,new)
s=s.replace('core.ptr.non_null.NonNull T','P').replace('ConstRawPtr T','Q').replace('core.slice.iter.Iter T','SourceIter P Q')
s=s.replace('{T : Type} {F : Type}', '{T P Q F : Type} (next : SourceIter P Q → Result ((Option T) × (SourceIter P Q)))')
assert s.count('(next :')==3
s=s.replace('core.slice.iter.IteratorSliceIter.next','next')
for name in ['anyBody','anyLoop','sourceAny']:
 s=re.sub(r'(?<![A-Za-z0-9_.])'+name+r'(?![A-Za-z0-9_.])','('+name+' next)',s)
 s=re.sub(r'def\s+\('+name+r' next\)','def '+name,s)
s=s.replace('def checkpoint_nonzero (bytes : Slice Std.U8)', 'def checkpoint_nonzero {P Q : Type} (next : SourceIter P Q → Result ((Option Std.U8) × SourceIter P Q)) (makeIter : Slice Std.U8 → Result (SourceIter P Q)) (bytes : Slice Std.U8)')
s=s.replace('core.slice.Slice.iter bytes','makeIter bytes')
head='''-- Control flow of the actual full-MIR std slice::Iter::any emission.
-- Pointer carriers and next are explicit parameters; no native instance is
-- inferred, and no pointer value, field, callback or short-circuit is erased.
import Aeneas
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisS2StdAnySource
structure SourceIter (P Q : Type) where
  ptr : P
  end_or_len : Q
  _marker : Unit

-- Literal emitted empty closure type (Unit).
@[reducible] def checkpoint_nonzero.closure := Unit

'''
out=head+s+'\n#print axioms anyBody\n#print axioms sourceAny\nend AspisS2StdAnySource\n'
(O/'S2StdAnySourceV1.lean').write_text(out)
sha=lambda t:hashlib.sha256(t.encode()).hexdigest()
(O/'std-any-emission-adapter.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw_funs_sha256=sha(raw),raw_types_sha256=sha(rawTypes),source_sha256=sha(out),changes=['retain all emitted body/loop/any, byte predicate, trait and caller definitions in full','remove metadata attributes only','rename declarations and namespace','generalize uninterpreted NonNull and ConstRawPtr carrier types to explicit type parameters','retain every actual Iter field in SourceIter, including the Unit marker','parameterize the reached next callee, with exactly the emitted input/output state type','thread next through the emitted loop and caller calls','parameterize the reached slice iterator constructor with its exact emitted state/output type'],qualification='Actual std any control flow with explicit physical-pointer carrier/next parameters. No custom axioms. A native iterator-state/next instance is still required; this is not an asserted SDK correspondence.'),indent=2)+'\n')
