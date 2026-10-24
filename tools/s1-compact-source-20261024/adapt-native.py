#!/usr/bin/env python3
"""Bind the emitted native semantic body, with one explicit value leaf."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021';I=E/'s1-native-compact-extraction/semantic/generated/AspisS1NativeCompact'
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
types='''import CurrentCompactCallerTypesV1
set_option autoImplicit false
namespace AspisS1NativeCompact
/-- Complete native codec-error carrier, shared with its actual caller. -/
abbrev compact.CodecError := AspisR1CurrentCaller.compact.CodecError
#print axioms AspisS1NativeCompact.compact.CodecError
end AspisS1NativeCompact
'''
raw=(I/'Funs.lean.txt').read_text();s=raw.replace('import AspisS1NativeCompact.Types','import S1NativeCompactTypesV1').replace('import AspisS1NativeCompact.FunsExternal\n','').replace('set_option maxHeartbeats 1000000\n','').replace('set_option maxRecDepth 2048\n','')
map={'compact.CodecError.Length':'AspisR1CurrentCaller.compact.CodecError.Length','compact.CodecError.NonZeroHigh':'AspisR1CurrentCaller.compact.CodecError.NonZeroHigh','compact.CodecError.NonCanonical':'AspisR1CurrentCaller.compact.CodecError.NonCanonical','compact.expand_values':'ops.expandValues','compact.expand_semantic_loop.body':'compact.expand_semantic_loop.body ops','compact.expand_semantic_loop':'compact.expand_semantic_loop ops','compact.expand_semantic':'compact.expand_semantic ops'}
pat=re.compile(r'(?<![A-Za-z0-9_.])(?:'+'|'.join(re.escape(n) for n in sorted(map,key=len,reverse=True))+r')(?![A-Za-z0-9_.])')
s=pat.sub(lambda m:map[m[0]],s)
# Avoid Lean local-binder shadowing of the emitted compact namespace.
parts=re.split(r'(--[^\n]*|/-.*?-/)',s,flags=re.S)
s=''.join(part if i%2 else re.sub(r'\bcompact\b(?!\.)','input',part) for i,part in enumerate(parts))
for n in ['compact.expand_semantic_loop.body','compact.expand_semantic_loop','compact.expand_semantic']:
 s=s.replace('def '+n+' ops\n','def '+n+' (ops : Ops)\n',1)
header='''
structure Ops where
  expandValues : (Slice U8) → (Slice U8) →
    Result ((core.result.Result Unit compact.CodecError) × Slice U8)

/-- Concrete standard Option::ok_or, preserving both Rust branches. -/
def core.option.Option.ok_or {T E : Type} (value : Option T) (error : E) :
    Result (core.result.Result T E) :=
  ok (match value with | some x => .Ok x | none => .Err error)

/-- Exact native source constant r1_wire.rs POINTS=3. -/
def r1_wire.POINTS : Result Usize := ok 3#usize
'''
s=s.replace('namespace AspisS1NativeCompact\n','namespace AspisS1NativeCompact\n'+header,1)
s=s.replace('end AspisS1NativeCompact','''#print axioms compact.expand_semantic_loop.body
#print axioms compact.expand_semantic
end AspisS1NativeCompact''',1)
for n,body in [('S1NativeCompactTypesV1',types),('S1NativeCompactModelV1',s)]:
 p=S/(n+'.lean')
 if '--check' in sys.argv:assert p.read_text()==body,n
 else:p.write_text(body)
manifest={'schema':'focused-extractor-proof-packet-v1','raw_body_sha256':sha(raw),'bound_body_sha256':sha(s),'identifier_map':map,'added_binder':'ops : Ops on semantic loop/body/entry; local compact renamed input to avoid namespace shadowing','concrete_leaves':['Option::ok_or','r1_wire::POINTS=3'],'remaining':['expand_values native/source instance','standard/runtime/caller association and totality proofs'],'qualification':'Only declared identifiers/binders/imports and concrete standard/constant leaves change; no native branch, loop, arithmetic, slice/lens or output carrier is replaced. Resource-option defaults from generated files are removed.'}
p=E/'s1-native-compact-adapter.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==manifest
else:p.write_text(json.dumps(manifest,indent=2)+'\n')
print('Native semantic body adapter checked' if '--check' in sys.argv else 'Native semantic body adapter generated')
