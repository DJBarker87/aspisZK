"""Task-level sequential declaration inventory; invokes the inherited compiler runner.
No launcher/monitor/admission implementation is changed. Each source snapshot
selects a different relevant declaration. Audits are not premise-removal credit.
"""
from pathlib import Path
import json,re,subprocess,sys
P=Path(__file__).resolve().parent; R=P.parents[1]
mods=['S2W_DigestExtraction','Port3_NativeBatchBody','Port9OR_Batch','Port9OR_BatchTree','Port9OR_BatchLoop','Port9OR_BatchStep','Port9OR_BatchProgress','Port9OR_P6Verify','Port9OR_P6Levels','Port9OR_P6Node','Port4B_LeafCode','Port4B_BatchJoin','Port4B_TreeJoin','BEl_PartialRecorder','BEl_Recorder','BEl_CodeCongr','BEl_LawComposition','BEh_Scope','BEj_SlotExport','BEk_ReachedInputs','BEk_CutExport','BEk_Returning','BEk_QueryPrefix','SdkC_Source','SdkC_BatchSource','SdkC_BatchPair','ARU_Returning','ARU_OriginalFactory','ARU_Support','ARU_OracleLog','ARU_SourceResults','ARU_PartialAccepted','ARX_Join','ARX_AdmittedRuntime','ARX_Residual','ARU_Charges','RPx_Transport','RPx_AccountCharge']
selected=[];seen=set()
for mod in mods:
 path=R/'lean'/(mod+'.lean')
 if not path.exists():path=R/'docs/research/100bit-spend-path-20261013/lean'/(mod+'.lean')
 source=path.read_text(); ns=re.search(r'^namespace (\S+)',source,re.M)
 if not ns:continue
 for raw in re.findall(r'^#print axioms (\S+)',source,re.M):
  name=raw if raw.startswith('Aspis') else ns[1]+'.'+raw
  if name not in seen:
   selected.append(dict(module=mod,declaration=name,source=str(path.relative_to(R))));seen.add(name)
assert len(selected)>=85,len(selected)
# Ensure account and bookkeeping endpoint audits are included alongside the syntax cuts.
last=[x for x in selected if x['module'] in mods[-8:]]
chosen=selected[:85-len(last)]+last
assert len(chosen)==85 and len({x['declaration'] for x in chosen})==85
(P/'BEn_AUDIT_PLAN.json').write_text(json.dumps(chosen,indent=2)+'\n')
for attempt,item in enumerate(chosen,15):
 source=f'''import BEn_Top
import BEn_Nonvacuity
import {item['module']}
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.maxSteps 1000000
set_option format.width 140
-- Focused extracted-trace provenance inventory: {item['source']}
#print {item['declaration']}
#print axioms {item['declaration']}
'''
 (R/'lean/BEn_TraceAudit.lean').write_text(source)
 result=subprocess.run([sys.executable,str(P/'BEn_compile.py'),str(attempt),'BEn_TraceAudit'],capture_output=True,text=True)
 (P/f'BEn_{attempt:03}-driver.log').write_text(result.stdout+result.stderr)
 print(f'{attempt:03} {item["declaration"]} exit={result.returncode}',flush=True)
 if result.returncode:sys.exit(result.returncode)
