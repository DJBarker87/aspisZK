#!/usr/bin/env python3
"""Reify hash nodes in retained semantic source bodies, full carriers unchanged."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
source=B/'lean-candidates/s1-prepared-claim-carrier-bridge-20261020/sources/AspisR1PublicPreparation/Funs.lean';raw=source.read_text()
selected=[('r1_wire.SemanticTranscript.sample_block_validated','sampleBlock'),('r1_wire.SemanticTranscript.semantic_validated','semanticValidated'),('r1_wire.begin','begin'),('r1_wire.SemanticTranscript.new','newTranscript'),('r1_semantic.public_transcript','publicTranscript'),('RoundModel.step','roundStep'),('RoundModel.rounds','rounds'),('FinishModel.circle_validated','circleValidated'),('FinishModel.finish','finish'),('VerifyPrefix.verify','verify')]
sha=lambda x:hashlib.sha256(x.encode()).hexdigest()
records=[]
for original,name in selected:
 if name=="begin":continue
 source0=source
 raw0=raw
 if original.startswith('RoundModel.'):source0=B/'lean/bridge-semantic-rounds-a555-20261017/ExtractedSemanticRoundsModel.lean';raw0=source0.read_text()
 elif original.startswith('FinishModel.'):source0=S/'S1SemanticFinishModelV1.lean';raw0=source0.read_text()
 elif original.startswith('VerifyPrefix.'):source0=S/'S1SemanticPrefixModelV1.lean';raw0=source0.read_text()
 match=re.search(r'^def\s+'+re.escape(original)+r'\s',raw0,re.M);assert match,original
 stop=re.search(r'^def\b|^#print|^end\b|^structure\b|^inductive\b',raw0[match.end():],re.M)
 end=match.end()+stop.start() if stop else len(raw0)
 doc=raw0.find('\n/--',match.end())
 if doc>=0:end=min(end,doc)
 text=raw0[match.start():end].rstrip();signature,body=text.split(':= do',1)
 signature=signature.replace('def '+original,'def '+name,1)
 outer=re.search(r'^  Result\b',signature,re.M);assert outer,original
 i=outer.start()+2
 signature=signature[:i]+'Code '+signature[i+7:]
 if name=='verify':signature=signature.replace('(F : VerifyPrefix.Finish)','(F : Finish)')
 body=body.replace('aspis_coreDigest32Inst.digest ','PreparedHashCode.effects.digest aspis_coreDigest32Inst ')
 body=re.sub(r'\bok\b','pure',body)
 for a,b in selected:body=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(a)+r'(?![A-Za-z0-9_.])',b,body)
 for a,b in selected:assert not re.search(r'(?<![A-Za-z0-9_.])'+re.escape(a)+r'(?![A-Za-z0-9_.])',body),(name,a)
 assert not re.search(r'aspis_coreDigest32Inst\.digest\b',body),name
 out='''import S1SemanticFinishModelV1
import S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode (Code)
\n'''+signature+':= do'+body+'\n\n#print axioms '+name+'\nend AspisR1PublicPreparation.S1SemanticCode\n'
 deps={'roundStep':'S1SemanticCodeSemanticValidatedV1','rounds':'S1SemanticCodeRoundStepV1','circleValidated':'S1SemanticCodeSampleBlockV1','finish':'S1SemanticCodeRoundsV1\nimport S1SemanticCodeCircleValidatedV1','verify':'S1SemanticCodeFinishV1\nimport S1SemanticCodeBeginV1\nimport S1SemanticCodePublicTranscriptV1','semanticValidated':'S1SemanticCodeSampleBlockV1','begin':'S1SemanticCodeSemanticValidatedV1','newTranscript':'S1SemanticCodeSampleBlockV1','publicTranscript':'S1SemanticCodeNewTranscriptV1'}
 if name in deps:out='import '+deps[name]+'\n'+out
 if name=='verify':out=out.replace('\ndef verify', '''
abbrev Finish := {H : Type} → aspis_core.Digest32 H →
  pool_v1.pair_forest_semantic_terminal.r0.Public → r1_wire.Prefix →
  r1_wire.SemanticTranscript H → r1_wire.Challenges → Option (verifier.Phase → Result Unit) →
  Code (core.result.Result (r1_semantic.Verified H) r1_wire.Error)

def verify''')
 target='S1SemanticCode'+name[0].upper()+name[1:]+'V1';p=S/(target+'.lean')
 if '--check' in sys.argv:assert p.read_text()==out
 else:p.write_text(out)
 records.append({'original':original,'target':target,'source_sha256':sha(text),'adapted_sha256':sha(out),'source_file':str(source0.relative_to(R))})
meta={'schema':'focused-extractor-proof-packet-v1','source_sha256':sha(raw),'targets':records,'changes':['Result-to-Code outer return monad','ok-to-pure constructors','Reify every direct digest call','Retain all full carriers, row checks, arithmetic, errors and non-hash child procedures'],'qualification':'Concrete source-body reification; source erasure, reply interpretation and enclosing caller composition must be checked separately.'};p=E/'s1-semantic-effects-source-pins.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==meta
else:p.write_text(json.dumps(meta,indent=2)+'\n')
print('Semantic effect source checked' if '--check' in sys.argv else 'Semantic effect source generated')
