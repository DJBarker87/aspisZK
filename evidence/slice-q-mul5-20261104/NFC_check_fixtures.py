from pathlib import Path
import json,hashlib,re,difflib
E=Path(__file__).resolve().parent;F=E.parent/'slice-q-mul4-20261104';P=E.parent/'axaudit2-20261102'
assert (F/'NFA_WALKER.lean').read_bytes()==(P/'NEP_WALKER.lean').read_bytes()
s=(F/'NFA_Driver.lean').read_text();t=(E/'NFC_Driver.lean').read_text()
addition='''if mode == "fixtures" then
      (#[`NEP_Planted, `NEP_Mutations],
       #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
         `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
         `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
    else if mode == "0" then'''
assert t==s.replace('if mode == "0" then',addition,1)
assert (E/'NFC_DRIVER.diff').read_text()==''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='NFA_Driver.lean',tofile='NFC_Driver.lean'))
log=(E/'NFC_L005/stdout.log').read_text();results=[json.loads(l.split('NEP_RESULT ',1)[1]) for l in log.splitlines() if l.startswith('NEP_RESULT ')]
expected={ 'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[] }
assert len(results)==8
for r in results:assert r['equal'] and r['walked_axioms']==r['collect_axioms']==expected[r['root']]
receipt=json.loads((E/'NFC_L005/receipt.json').read_text());assert receipt['exit_status']==0
old=json.loads((F/'NFA_AUDIT.json').read_text());assert old['unique_roots']==152 and old['zero_unresolved_constants'] and old['standard_axioms_only']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
obj=json.loads((E/'NFC_L003/receipt.json').read_text())['deps_fingerprint']['selected_objects']
out=dict(status='PASS_AX2_CONDITION_3',walker_unchanged=True,walker_sha256=sha(F/'NFA_WALKER.lean'),driver_diff_sha256=sha(E/'NFC_DRIVER.diff'),fixtures=results,fixture_sources={str(P/n):sha(P/n) for n in ['NEP_Planted.lean','NEP_Mutations.lean']},fixture_objects={k:v for k,v in obj.items() if 'NEP_Planted' in k or 'NEP_Mutations' in k},fixture_receipt='NFC_L005/receipt.json',print_axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log),inherited_audit=dict(path=str(F/'NFA_AUDIT.json'),sha256=sha(F/'NFA_AUDIT.json'),unique_roots=152,rerun=False),rows_credited=['TX1:185','TX2:111','TX1:182','TX2:108'],credit='Inherited NEV local composed rows admitted by ax2; no incoming caller edge or slice-root closure',security_target_established=False)
previous=json.loads((E/'NFC_AUDIT.json').read_text()) if (E/'NFC_AUDIT.json').exists() else {}
if 'standalone_NFC' in previous:out['standalone_NFC']=previous['standalone_NFC']
(E/'NFC_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS: eight fixture roots; four NEV rows admitted')
