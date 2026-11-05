"""Additive evidence checks and denial controls; never grants native row credit."""
from pathlib import Path
import json,hashlib,lzma,re,copy,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
load=lambda n:json.loads((E/n).read_text())
expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
def check(a,d):
 assert a['status']=='PASS_CONDITIONAL_MODEL_SIDE_AX2'
 assert d['promotions']==d['status_changes']==d['trust_changes']==[]
 assert d['targets']=={'TX1:087':'OPEN','TX1:094':'OPEN','TX1:179':'OPEN'}
 assert a['native_or_composed_promotions']==0 and a['trust_changes']==[]
 assert a['frozen_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 assert a['headline']=='AspisR1.RPx_Deployed.deployed'
 assert a['budget']['kani_used']==0 and a['budget']['extraction_used']==2 and a['budget']['lean_support_used']<=80
 assert a['driver_core_byte_identical_to_NEP'] and a['walker_unchanged']
 assert a['standard_axioms_only'] and a['raw_equals_collect'] and a['no_XRn_Join']
 assert a['root_count']==62 and len(a['roots'])==62
 assert all(r['equal'] and r['collect_axioms']==r['walked_axioms'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in a['roots'])
 assert len(a['fixtures'])==8 and all(r['equal'] and r['walked_axioms']==expected[r['root']] and r['collect_axioms']==expected[r['root']] for r in a['fixtures'])
 assert a['scan']['exit']==a['scan']['dangling']==a['scan']['incompatible_owners']==a['scan']['import_mismatches']==0
 assert all(r['exit_status']==0 for r in a['selected_receipts'])
a=load('NHL_AUDIT.json');d=load('NHL_LEDGER_DELTA.json');check(a,d)
for pin in load('NHL_RAW_AUDIT_PINS.json'):
 p=R/pin['path'];raw=lzma.decompress(p.read_bytes())
 assert hashlib.sha256(p.read_bytes()).hexdigest()==pin['sha256'] and hashlib.sha256(raw).hexdigest()==pin['raw_sha256']
closure=lzma.decompress((E/'NHL_CLOSURE_PINS.json.xz').read_bytes())
assert hashlib.sha256(closure).hexdigest()==(E/'NHL_CLOSURE_PINS.json.sha256').read_text().strip()
assert load('NHL_HOST_FINAL.json')['all_submitted_terminal']
required=['NHL_OPACITY.md','NHL_HYPOTHESES.md','NHL_PrepareModel.lean','NHL_Tx1Model.lean','NHL_PreparedRecompose.lean','NHL_BRIDGES.md','NHL_LEDGER_DELTA.json','NHL_AUDIT.json','NHL_COMBINED_IMPORT.lean','NHL_HANDOFF.md','NHL_REMAINING.md','NHL_ATTEMPTS.jsonl']
assert all((E/n).is_file() for n in required)
# No compiled module imports raw external templates or adds an admission/axiom.
for p in E.glob('NHL_*.lean'):
 text=p.read_text();assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text),p
 assert 'import NHL_Actual' not in text
 if p.stem not in ['NHL_EmittedPrepare','NHL_EmittedTx1']:assert not re.search(r'set_option (maxHeartbeats|maxRecDepth)',text)
assert not any(p.stat().st_size>20*1024*1024 for p in E.rglob('*') if p.is_file())
assert not list(E.rglob('__pycache__'))
# Check the exact compiler-input snapshot of every current Lean source.
latest={}
for line in (E/'NHL_ATTEMPTS.jsonl').read_text().splitlines():
 r=json.loads(line)
 if r['kind']=='lean' and r['exit_status']==0:latest[r['module']]=r['attempt']
for p in E.glob('NHL_*.lean'):
 assert p.stem in latest,p.name
 original=E/latest[p.stem]/'sources/NHL_generated'/p.name
 assert p.read_bytes()==original.read_bytes(),p.name
assert hashlib.sha256((R/d['baseline']).read_bytes()).hexdigest()==d['baseline_sha256']
for name in ['crates','programs']:
 assert subprocess.check_output(['git','rev-parse','HEAD:'+name],text=True)==subprocess.check_output(['git','rev-parse',a['frozen_revision']+':'+name],text=True)
denials=[]
for name,mutate in [
 ('premature_promotion',lambda x,y:y['promotions'].append({'row':'TX1:087'})),
 ('trust_removal',lambda x,y:x['trust_changes'].append('removed P6')),
 ('unauthorized_kani',lambda x,y:x['budget'].__setitem__('kani_used',1)),
 ('nonstandard_axiom',lambda x,y:x['roots'][0].__setitem__('walked_axioms',['sorryAx'])),
 ('import_mismatch',lambda x,y:x['scan'].__setitem__('import_mismatches',1)),
 ('missing_fixture_axiom',lambda x,y:x['fixtures'][0].__setitem__('walked_axioms',[])),
 ('changed_driver_core',lambda x,y:x.__setitem__('driver_core_byte_identical_to_NEP',False)),
 ('wrong_freeze',lambda x,y:x.__setitem__('frozen_revision','wrong')),
 ('failed_selected_gate',lambda x,y:x['selected_receipts'][0].__setitem__('exit_status',1)),
 ('raw_collect_disagreement',lambda x,y:x.__setitem__('raw_equals_collect',False))]:
 x=copy.deepcopy(a);y=copy.deepcopy(d);mutate(x,y)
 try:check(x,y)
 except AssertionError:denials.append(name)
 else:raise AssertionError('mutation was admitted: '+name)
(E/'NHL_VALIDATION.json').write_text(json.dumps({'exit':0,'denials':denials,'native_promotions':0,'required_outputs':required},indent=1)+'\n')
print('PASS: conditional evidence, zero promotions, ten denial controls')
