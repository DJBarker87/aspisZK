"""Fresh multiplication-free reducer/finisher evidence, exact source and models."""
from pathlib import Path
import json,hashlib,re
from NEI_native_pair import check
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
P='crates/aspis-r1-cost-probe/src/fast_pairing.rs::'
FUNCTIONS=[P+n for n in ['canonical::reduce','canonical::Q::limbs','canonical::Dot::finish','EbyKDot::finish']]
PAIRS=dict(zip(FUNCTIONS,[['NEI_K043','NEI_K044','NEI_wrong_reduce_word'],['NEI_K049','NEI_K050','NEI_wrong_q_limbs'],['NEI_K045','NEI_K046','NEI_wrong_dot_finish'],['NEI_K047','NEI_K048','NEI_wrong_eby_finish']]))
APPROVED_MODEL_SHA={'NEI_DotReduction': '3a9724041f847a940d491491266f90ddb013bcababe9c0819437925a58b39f33', 'NEI_ReduceRefLaw': '94388a0075bd7d363a2913f7ba9919b887a358149b7fb1b111852a2a3ea7b3fd', 'NEI_DotFinishFrames': '8b819d0aadedbc9731d41c673728329e7418deacc8e1e398aba658807d5eb49c', 'NEI_DotFinishAssociation': 'a1b6ddfc55a1bfa45d7b118aeaf6352bf551fae3406a38ffe16f355d4d005aa6', 'NEI_DotFinishValues': '7ed049144ccf199f7004a1423601d609e9e42fb684b00fa254959747409b717b', 'NEI_EbyFinishAssociation': 'e94a416e46684e83da20513a2b00aedf8a0b35978a9091890792648ee48b20f0', 'NEI_PublicDotFinishValues': '71603fbd603af30e5a939a0b2a894cbecebc00ca481bebc278e775558dae2a63', 'NEI_WideCtorAssociation': '61e44c7a5ed8655cf66c7d4c30be40ffd2d637b5f2202ad62ea1e20823a7180b'}
APPROVED_NATIVE_SHA='b412715a2b0893538feed723cd406dcc23b6cce63763c9b033661978a398278e'
def audit(E,R,p,neb,require):
 require(p['function'] in FUNCTIONS and p['route']=='D188_ACTUAL_DOT_FINISH' and p['status']=='CLOSED-CONDITIONAL','finisher scope/route')
 require(p['domain']=='All valid typed inputs; raw words unrestricted; count unrestricted' and p['remaining_inner_hypotheses']==[] and p['suspended_neb_credits_restored']==[],'finisher domain/credit')
 require(p['native_pair']==PAIRS[p['function']],'unregistered finisher pair')
 required={'NEI_DotReduction.constant_cast','NEI_DotReduction.same','NEI_DotReduction.value','NEI_ReduceRefLaw.same','NEI_ReduceRefLaw.actual_reference','NEI_ReduceRefLaw.frame'}
 extra=[set(),{'NEI_DotFinishAssociation.limbs'},{'NEI_DotFinishAssociation.finish','NEI_DotFinishValues.source'},{'NEI_EbyFinishAssociation.same','NEI_EbyFinishAssociation.ctor_unwrap','NEI_PublicDotFinishValues.source','NEI_WideCtorAssociation.same_result'}][FUNCTIONS.index(p['function'])]
 required|=extra|{'NEI_DotFinishFrames.'+['reduce','limbs','dot','outer'][FUNCTIONS.index(p['function'])]}
 require(required<={t for e in p['lean_evidence'] for t in e['theorems']},'missing specific result/domain/frame theorem')
 for module,h in APPROVED_MODEL_SHA.items():require(sha(E/(module+'.lean'))==h,'unreviewed model statement/source')
 for proof in p['lean_evidence']:
  for theorem in proof['theorems']:neb.check_receipt(proof,theorem)
  d=obj(R/proof['receipt'])
  for path,h in d['source_hashes'].items():require(sha(E/path.removeprefix('NEI_generated/'))==h,'finisher successful source changed')
 first=obj(E/'NEI_E001/NEI_EXTRACTION_PINS.json')
 for a,namespace in [('NEI_E009','NEI_DotFinishRaw'),('NEI_E010','NEI_ReduceRefRaw')]:
  ex=obj(E/a/'NEI_EXTRACTION_PINS.json');require(ex['exit']==0 and ex['charon_exit']==0 and ex['lock_before']==ex['lock_after'],'finisher extraction/lock')
  require(all(ex[k]==first[k] for k in ['charon_sha256','aeneas_sha256','toolchain']),'finisher translator pins')
  for path,h in ex['outputs'].items():
   raw=E/(path+'.txt' if path.endswith('_Template.lean') else path);require(sha(raw)==h,'changed extraction output')
   if path.endswith('_Template.lean'):continue
   require(sha(E/namespace/Path(path).name)==h,'changed working actual/reference body')
   require(not re.search(r'\b(axiom|sorry|admit|native_decide)\b',raw.read_text()),'admitted emitted body')
 frozen=obj(E/'NEI_FROZEN.json')['crates/aspis-r1-cost-probe/src/fast_pairing.rs'];end=frozen.index('/// Candidate exact accumulator for sums of `WideExact * WideExact`.')
 require((E/'NEI_E009/NEI_isolation_src_NEI_pairing.rs.txt').read_text()==frozen[:end],'changed actual pairing prefix')
 base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');rows=[r for r in base['rows'] if r['function']==p['function']]
 require(rows and all(r['frozen_body_sha256']==p['source_body_sha256'] for r in rows) and p['frozen_revision']==base['frozen_revision'],'finisher source/body')
 pair=check(E,*p['native_pair'])
 native=(E/p['native_pair'][0]/'sources/NEI_src/crates/aspis-r1-cost-probe/src/NEI_dot_ctor.rs').read_text()
 require(hashlib.sha256(native.encode()).hexdigest()==APPROVED_NATIVE_SHA,'unreviewed native comparison/context')
 reference=(E/'NEI_E010/NEI_isolation_src_lib.rs.txt').read_text()
 from NEI_validate import function
 require(function(native,'NEI_reduce_ref')==function(reference,'NEI_reduce_ref'),'compiled native reference differs from extracted reference')
 require(reference.startswith('const P:u32=2147483647;\n') and 'NEI_DotReduction.constant_cast' in [t for q in p['lean_evidence'] for t in q['theorems']],'reference modulus not bound')
 require(sha(R/p['review']['path'])==p['review']['sha256'],'finisher review changed')
 return dict(function=p['function'],status=p['status'],route=p['route'],native_pair=pair,composed_rows_closed=[])
def check_cast(row,o,ext,rc):
 assert row['function']==FUNCTIONS[0] and o['call'].get('expression',o['call'].get('syntax'))=='u64::from','not private modulus cast'
 assert ext['source_value']==2147483647 and ext['line']==o['call']['line'] and ext['line'] in [11,12,13],'wrong constant/site'
 assert ext['caller_body_sha256']==row['frozen_body_sha256'] and ext['native_review']==rc['native_review'],'wrong cast native context'
 assert ext['theorems']==['NEI_DotReduction.constant_cast'] and any(ext['theorems'][0] in e['theorems'] for e in rc['lean_evidence']),'missing exact cast theorem'

def check_finish_external(row,o,ext,index,base,approved_edges,rc,validator):
 syntax=o['call'].get('expression',o['call'].get('syntax'))
 assert ext['source_body_sha256']==row['frozen_body_sha256'] and ext['line']==o['call']['line'] and ext['syntax']==syntax,'wrong exact finisher boundary'
 if ext['kind']=='NEI_DOT_VALUE_CTOR':
  assert row['function']==FUNCTIONS[2] and syntax=='Q' and ext['line']==123,'Q constructor belongs to another function/site'
  assert ext['theorems']==['NEI_DotFinishAssociation.finish'],'missing exact four-field constructor result'
 else:
  assert ext['kind']=='NEI_EBY_CTOR_UNWRAP' and row['function']==FUNCTIONS[3] and ext['line']==180 and syntax=='E::from_limbs([a,b,c,d,e,f,g,h]).unwrap','not actual outer unwrap'
  callee='crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs';edge=row['function']+' -> '+callee
  assert ext['callee']==callee and ext['edge']==edge,'wrong constructor callee'
  obligation=index['call-domain:'+row['function']+'->'+callee]
  assert obligation['certificate']==approved_edges[edge],'constructor edge not independently certified'
  assert not validator.certificate_errors(obligation,obligation['certificate'],base),'constructor edge invalid'
  assert ext['theorems']==['NEI_EbyFinishAssociation.ctor_unwrap','NEI_PublicDotFinishValues.source'],'missing all-Result unwrap/canonical success laws'
 assert all(any(t in p['theorems'] for p in rc['lean_evidence']) for t in ext['theorems']),'finisher external law not audited'
