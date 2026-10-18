#!/usr/bin/env python3
"""Stage exact proof-only Public/sigma import splits; no compiler."""
from pathlib import Path
import json,re,hashlib,difflib
O=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/bridge/sources');W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-selected-current-20261017');S=W/'split-sources';S.mkdir(parents=True,exist_ok=True);sha=lambda b:hashlib.sha256(b).hexdigest();records=[]
def read(n):return(O/(n.replace('.','/')+'.lean')).read_text()
def save(n,text):p=S/(n.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
raw=read('R1UnifiedSampler');at=raw.index('structure Public (L : Nat) where');end=raw.index('\nabbrev Prefix',at);decl=raw[at:end].rstrip()+'\n';small='''import AspisV8R19.DuplexFrames
set_option autoImplicit false
namespace AspisR1.UnifiedSampler
open AspisV8R19.DuplexFrames
'''+decl+'\n#print axioms Public\nend AspisR1.UnifiedSampler\n';save('R1UnifiedSamplerPublic',small)
new=raw[:at]+raw[end:];new='import R1UnifiedSamplerPublic\n'+new;assert new.removeprefix('import R1UnifiedSamplerPublic\n')[:at]+decl.rstrip()+'\n'+raw[end:]==raw # exact inverse
save('R1UnifiedSampler',new);records.append({'module':'R1UnifiedSampler','moved_qualified_declarations':['AspisR1.UnifiedSampler.Public'],'exact_original_declaration_sha256':sha(decl.encode()),'original_source_sha256':sha(raw.encode()),'split_source_sha256':sha(new.encode()),'new_core':'R1UnifiedSamplerPublic','new_core_sha256':sha(small.encode()),'inverse_recovers_original':True,'source_diff':''.join(difflib.unified_diff(raw.splitlines(True),new.splitlines(True),fromfile='old',tofile='split'))})
raw=read('R1SelectedChallengeMap');start=raw.index('def sigma ');end=raw.index('\ntheorem gamma_row',start);decl=raw[start:end].rstrip()+'\n';assert decl.count('\ndef rhoOf ')==1 and decl.count('\ntheorem semantic_row ')==1
small='''import R0C.ModuloField
import R0P.SemD2
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedChallengeMap
open AspisV8R19.SourceDuplexStep AspisWideTower AspisCircleGroupOrder
open R0P.SemSource
'''+decl+'\n#print axioms sigma\n#print axioms rhoOf\n#print axioms semantic_row\nend AspisR1.SelectedChallengeMap\nend\n';save('R1SelectedChallengeMapCore',small)
new=raw[:start]+raw[end:];new='import R1SelectedChallengeMapCore\n'+new;assert new.removeprefix('import R1SelectedChallengeMapCore\n')[:start]+decl.rstrip()+'\n'+raw[end:]==raw;save('R1SelectedChallengeMap',new);records.append({'module':'R1SelectedChallengeMap','moved_qualified_declarations':['AspisR1.SelectedChallengeMap.sigma','AspisR1.SelectedChallengeMap.rhoOf','AspisR1.SelectedChallengeMap.semantic_row'],'exact_original_declaration_sha256':sha(decl.encode()),'original_source_sha256':sha(raw.encode()),'split_source_sha256':sha(new.encode()),'new_core':'R1SelectedChallengeMapCore','new_core_sha256':sha(small.encode()),'inverse_recovers_original':True,'source_diff':''.join(difflib.unified_diff(raw.splitlines(True),new.splitlines(True),fromfile='old',tofile='split'))})
raw=read('R1SelectedTranscriptParams');new=raw.replace('import R1SelectedChallengeMap\nimport R1UnifiedSampler\n','import R1SelectedChallengeMapCore\nimport R1UnifiedSamplerPublic\n',1).replace('open AspisR1.TranscriptView\n','',1);assert new.replace('import R1SelectedChallengeMapCore\nimport R1UnifiedSamplerPublic\n','import R1SelectedChallengeMap\nimport R1UnifiedSampler\n',1).replace('open AspisV8R19.SourceDuplexStep\n','open AspisV8R19.SourceDuplexStep\nopen AspisR1.TranscriptView\n',1)==raw;save('R1SelectedTranscriptParams',new);records.append({'module':'R1SelectedTranscriptParams','original_source_sha256':sha(raw.encode()),'split_source_sha256':sha(new.encode()),'all_declaration_bodies_unchanged':True,'inverse_recovers_original':True,'removed_open':'AspisR1.TranscriptView (unused; Byte/Bytes supplied by existing DuplexFrames/SourceDuplexStep)','source_diff':''.join(difflib.unified_diff(raw.splitlines(True),new.splitlines(True),fromfile='old',tofile='split'))})
raw=read('R1SelectedCompletedSemantic');new=raw.replace('import R1SelectedChallengeMap\n','import R1SelectedChallengeMapCore\n',1);assert new.replace('import R1SelectedChallengeMapCore\n','import R1SelectedChallengeMap\n',1)==raw;save('R1SelectedCompletedSemantic',new);records.append({'module':'R1SelectedCompletedSemantic','original_source_sha256':sha(raw.encode()),'split_source_sha256':sha(new.encode()),'all_declaration_bodies_unchanged':True,'inverse_recovers_original':True,'source_diff':''.join(difflib.unified_diff(raw.splitlines(True),new.splitlines(True),fromfile='old',tofile='split'))})
(W/'proof-import-split-audit.json').write_text(json.dumps(records,indent=2)+'\n');print('STAGED6 proof-only sources; exact Public/sigma/rhoOf/semantic_row moved; source inverses passed; no compiler')
