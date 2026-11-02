"""Prepare the final audit/replays only after all focused source targets pass."""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd5-20261101';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
plan=json.load(open(E/'source-resolution.json'));pre=json.load(open(E/'preflight-result.json'));accepted=dict(pre['reused']);names=set()
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.load(open(p))
 if j['exit'] or j['attempt']>=78297:continue
 source=R/j['source_path']
 if hashlib.sha256(source.read_bytes()).hexdigest()!=j['source_sha256']:continue
 accepted[j['module']]=j
 for x in j['axioms']:
  assert 'sorryAx' not in x
  names.add(re.match(r"'([^']+)'",x)[1])
for m,pin in plan['modules'].items():
 key=m.replace('.','/');assert key in accepted,('focused target not compiled',key)
 assert accepted[key]['source_sha256']==pin['sha256']==hashlib.sha256((R/pin['path']).read_bytes()).hexdigest(),key
 if 'PV_RDCD5_' in m:
  s=(R/pin['path']).read_text();ns=re.search(r'^namespace\s+(\S+)',s,re.M)[1]
  for name in re.findall(r'^theorem\s+(\S+)',s,re.M):names.add(ns+'.'+name)
for m in ['PV_RDCD5_V233','PV_RDCD5_V236','PV_RDCD5_UpdateSplit','PV_RDCD5_ParserErrors']:assert 'R1Z/'+m in accepted
rows=json.load(open(E/'ROWS.json'));assert rows['V197']['status']=='FINDING'
assert all(rows[n]['status']=='RESTORED' for n in ['V233','V236']), 'commit precise row restoration before audit'
imports=''.join('import '+m+'\n' for m in sorted(plan['modules']))
checks='\n'.join('#check @'+x for x in sorted(names))+'\n'
(L/'PV_RDCD5_FinalAudit.lean').write_text(imports+'\n'+checks+''.join('#print axioms '+x+'\n' for x in sorted(names)))
# Replay exactly the original typed interfaces by named applications.
s='''import R1Z.PV_RDCD5_FinalAudit
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD5_FocusedReplay
open Aeneas Aeneas.Std Result ProverRwFull PV_CBL_LibraryShapes PV_CBL_GenericArrayPower
'''
for module,old,new,application in [
 ('PV_RDCD5_V233','consumed_instance','v233','PV_RDCD5_V233.consumed_instance base ops input origin'),
 ('PV_RDCD5_V236','op216_instance','v236','PV_RDCD5_V236.op216_instance base ops uc less nz self input hp')]:
 source=(L/(module+'.lean')).read_text();start=source.index('theorem '+old);end=source.index(':= by',start)
 declaration=source[start:end].replace('theorem '+old,'theorem '+new,1)
 s+='\n'+declaration+':= by\n  exact '+application+'\n#print axioms '+new+'\n'
s+='''
theorem v197_finding :
    ProverRwSuccessParserSource.aspis_core.field.QM31.from_le_bytes
      (⟨[],by simp⟩ : Slice U8) ≠ PV_RDCD4_BytesSource.qm [] :=
  PV_RDCD5_ParserErrors.carrier_mismatch
#print axioms v197_finding
end R1Z.PV_RDCD5_FocusedReplay
'''
(L/'PV_RDCD5_FocusedReplay.lean').write_text(s)
t='import R1Z.PV_RDCD5_FocusedReplay\n'
for name in ['v233','v236','v197_finding']:
 t+='#check @R1Z.PV_RDCD5_FocusedReplay.'+name+'\n#print axioms R1Z.PV_RDCD5_FocusedReplay.'+name+'\n'
(L/'PV_RDCD5_FrozenManifest.lean').write_text(t)
(E/'final-source-freeze.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),modules=plan['modules'],printed_declarations=sorted(names),restored_rows=['V233','V236'],finding_rows=['V197'],scope='Exact complete Result and typed carrier interfaces; standard axioms; no endpoint premise removed, added or changed'),indent=2)+'\n')
print('Prepared',len(plan['modules']),'module frozen cohort;',len(names),'statement/axioms queries; focused typed replay and one final manifest')
