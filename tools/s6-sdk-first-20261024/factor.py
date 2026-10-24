#!/usr/bin/env python3
"""Dependency factor: copy exact published declarations without editing bodies."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';P=B/'evidence/s126-current-caller-20261021/s6-sdk-first-factor-20261024';P.mkdir(exist_ok=True)
revision='97caa13d92';out=[];rows=[]
def take(module,start,end,header,footer):
 path=str((B/'lean'/(module+'.lean')).relative_to(R));src=subprocess.check_output(['git','show',revision+':'+path],cwd=R).decode();assert src.count(start)==1,(module,start)
 pos=src.index(start);stop=src.index(end,pos) if end is not None else len(src);body=src[pos:stop]
 out.append(header+body+footer)
 rows.append(dict(module=module,revision=revision,path=path,source_sha256=hashlib.sha256(src.encode()).hexdigest(),start=start,end=end,header=header,footer=footer,body_sha256=hashlib.sha256(body.encode()).hexdigest()))
imports='''import S2W_WrapperLaws
import S2W_Trace
import S2W_EntryPrivileges
import S2W_SnapshotFacts
import AspisV8R19.SqueezeOracleBridge
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
'''
take('MultiproofConeCanonical','def bytesOf','\nprivate theorem','namespace AspisR1.MultiproofConeCanonical\nopen AspisV8R19.DuplexFrames\n','end AspisR1.MultiproofConeCanonical\n')
take('S2LeadInterface','structure Account where','/-- Data supplied','namespace AspisR1.S2LeadInterface\nopen AspisV8R19.DuplexFrames\n','end AspisR1.S2LeadInterface\n')
take('S2Z_Oracle','abbrev Parts :=','/-- Nominal', 'namespace AspisR1.S2Z.Oracle\n','end AspisR1.S2Z.Oracle\n')
take('S2W_ExtractionBoundary','abbrev Accounts :=','/-- Exactly the project','namespace AspisR1.S2W_ExtractionBoundary\nopen Aeneas Aeneas.Std Result AspisR1.AdapterRw\n','end AspisR1.S2W_ExtractionBoundary\n')
take('S2W_EntryWriteHistory','def payloadBytes','/-- Pointwise wrapper','namespace AspisR1.S2W_EntryWriteHistory\nopen S2Trust AspisV8R19.DuplexFrames\n','end AspisR1.S2W_EntryWriteHistory\n')
take('S2W_CommittedCheckpoint','def source','/-- Kani', 'namespace AspisR1.S2W_CommittedCheckpoint\nopen S2Trust S2W_EntryWriteHistory\n','end AspisR1.S2W_CommittedCheckpoint\n')
take('S2W_ReturnedCheckpoint','namespace AspisR1.S2W_ReturnedCheckpoint','/-- The loaded version','','end AspisR1.S2W_ReturnedCheckpoint\n')
take('S2W_AccountObservations','namespace AspisR1.S2W_AccountObservations',None,'','\n')
take('S2W_D189Interpretation','namespace AspisR1.S2W_D189Interpretation','/-- State extension', '', 'end AspisR1.S2W_D189Interpretation\n')
take('S2W_SnapshotJoin','namespace AspisR1.S2W.SnapshotJoin','/-- The previous snapshot', '', 'end AspisR1.S2W.SnapshotJoin\n')
# Entire entry and wrapper modules after their module-level boilerplate.
for module in ['S2W_D189Entry','S2W_D189Wrappers']:
 take(module,'namespace AspisR1.'+module,'\nend\n','','\n')
take('S2W_DigestExtraction','namespace AspisR1.S2W_DigestExtraction','/-- NativeBinding', '', 'end AspisR1.S2W_DigestExtraction\n')
take('S2W_D189Consolidation','structure RuntimeEntrypointAdmission','\ndef before','namespace AspisR1.S2W_D189Consolidation\nopen S2Trust S2W_D189Entry S2W_ReturnedCheckpoint\n','end AspisR1.S2W_D189Consolidation\n')
content=imports+'\n'.join(out)+'\nend\n'
path=S/'S6SdkDependencyFactorV1.lean'
if '--check' in sys.argv:assert path.read_text()==content
else:path.write_text(content)
manifest=dict(schema='focused-extractor-proof-packet-v1',imports=imports,selections=rows,source=str(path.relative_to(R)),source_sha256=hashlib.sha256(content.encode()).hexdigest(),scope='Literal declaration dependency factor. Full original account/SDK/heap/allocator/entry/wrapper/extraction carriers, operations, errors and selected proofs are unchanged under identical namespaces. Unrelated security joins are not imported. Not a full original-module/release replay.')
if '--check' in sys.argv:assert json.loads((P/'declarations.json').read_text())==manifest
else:(P/'declarations.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(status='PASS',selections=len(rows),bytes=len(content.encode()))))
