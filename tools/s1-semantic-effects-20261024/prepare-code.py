#!/usr/bin/env python3
from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021';source=S/'CurrentCompactCallerModelV1.lean';raw=source.read_text();start=raw.index('def verifier.candidate.prepare (ops : Ops)');end=raw.index('\n/--',start);text=raw[start:end].rstrip();signature,body=text.split(':= do',1)
signature=signature.replace('def verifier.candidate.prepare (ops : Ops)','''def prepare (base : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)''',1)
signature=re.sub(r'  \(obs : Option \(verifier.Phase → Result Unit\)\)\n','',signature)
match=re.search(r'^  Result\b',signature,re.M);assert match;i=match.start()+2;signature=signature[:i]+'Code'+signature[i+6:]
body=re.sub(r'\bobs\b','none',body)
body=body.replace('ops.op9 aspis_coredigestDigest32Inst public1\n              v.semantic hash none','S1SemanticCodeInstallation.code R B aspis_coredigestDigest32Inst public1\n              v.semantic hash')
body=body.replace('ops.op8 aspis_coredigestDigest32Inst val2 v hash g','BorrowedClaimPrepared.closedPreparationCode aspis_coredigestDigest32Inst val2 v hash g')
body=re.sub(r'\bok\b','pure',body)
out='''import S1SemanticCurrentCodeV1
import S1ClosedPreparationHashCodeV1
import S1NativePrepareBuffersV1
import S1ValuesOwnedInstallationV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.S1PrepareCode
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisS1ValuesOwnedInstallation

'''+signature+''':= do
  let ops := BorrowedClaimPrepared.NativeBuffers.install (withValues base) nativeValues R B
'''+body+'\n\n#print axioms prepare\nend AspisR1CurrentCaller.S1PrepareCode\n'
p=S/'S1CurrentPrepareCodeV1.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
meta={'schema':'focused-extractor-proof-packet-v1','source_sha256':hashlib.sha256(text.encode()).hexdigest(),'generated_sha256':hashlib.sha256(out.encode()).hexdigest(),'changes':['Fix observer to release None','Use the same full installed operation record','Reify complete semantic and original Prepared::new bodies','Lift other original Result steps without changing errors, values or branch order'],'qualification':'Source model effect reification; other lower port associations and actual SDK/runtime effects remain explicit.'};p=E/'s1-current-prepare-code-source-pins.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==meta
else:p.write_text(json.dumps(meta,indent=2)+'\n')
