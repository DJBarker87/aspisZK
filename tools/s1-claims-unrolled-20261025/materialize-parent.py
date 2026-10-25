#!/usr/bin/env python3
"""Expose only four emitted primitive ports as ordinary function parameters."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
p=B/'evidence/s126-current-caller-20261021/s1-claims-nuc-extract-run10/generated/AspisS1ClaimsUnrolledSource/Funs.lean';raw=p.read_text();matches=list(re.finditer(r'(?m)^def\s+([A-Za-z0-9_.]+)',raw))
parts=[];pins=[]
for k,m in enumerate(matches):
 name=m[1]
 if name not in ['aspis_core.r0.heap.filled','candidate_claims.claims']:continue
 start=raw.rfind('/--',0,m.start());end=raw.rfind('/--',0,matches[k+1].start())if k+1<len(matches)else raw.index('\nend AspisS1ClaimsUnrolledSource',m.end())
 chunk=raw[start:end];before=chunk
 if name.endswith('filled'):chunk=chunk.replace('{T : Type} (coremarkerCopyInst','{T : Type} (backend : PrimitivePorts) (coremarkerCopyInst')
 else:chunk=chunk.replace('(prefix1 : r1_wire.Prefix)','(backend : PrimitivePorts) (prefix1 : r1_wire.Prefix)')
 for a,b in [('alloc.vec.Vec.try_reserve_exact','backend.reserve'),('alloc.vec.Vec.into_boxed_slice','backend.intoBox'),('BoxArray.Insts.CoreConvertTryFromBoxSliceBoxSlice.try_from','backend.toArray'),('r1_wire.ValidatedRecord.decode_k','backend.decode')]:chunk=chunk.replace(a,b)
 if name=='candidate_claims.claims':chunk=chunk.replace('aspis_core.r0.heap.filled (','aspis_core.r0.heap.filled backend (')
 parts.append(chunk);pins.append(dict(name=name,raw_sha256=hashlib.sha256(before.encode()).hexdigest(),parameterized_sha256=hashlib.sha256(chunk.encode()).hexdigest()))
s='''import S1ClaimsSourceReadsV1
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisS1ClaimsUnrolledSource
/-- Four unresolved emitted primitives, as functions rather than axioms.
No concrete native instance or successful execution is asserted here. -/
structure PrimitivePorts where
  reserve : {T : Type} → (A : Type) → alloc.vec.Vec T → Std.Usize →
    Result ((core.result.Result Unit alloc.collections.TryReserveError) × alloc.vec.Vec T)
  intoBox : {T : Type} → (A : Type) → alloc.vec.Vec T → Result (Slice T)
  toArray : {T : Type} → (N : Std.Usize) → Slice T →
    Result (core.result.Result (Array T N) (Slice T))
  decode : (N : Std.Usize) → r1_wire.ValidatedRecord → Std.Usize →
    Result (core.result.Result (Array aspis_core.field.QM31 N) r1_wire.Error)

'''+''.join(parts)+'\nend AspisS1ClaimsUnrolledSource\n'
s+='\n#print axioms AspisS1ClaimsUnrolledSource.aspis_core.r0.heap.filled\n#print axioms AspisS1ClaimsUnrolledSource.candidate_claims.claims\n'
out=B/'lean-candidates/s126-caller-boundary-20261021/S1ClaimsUnrolledParentV1.lean';out.write_text(s)
(Path(__file__).parent/'parent-binding.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),maintained_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),complete_declarations=pins,primitive_ports=4,concrete_native_instance=False,resource_options=False),indent=2)+'\n')
