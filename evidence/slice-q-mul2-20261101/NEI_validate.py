"""Additive D188 actual-body packet audit; original NEB receipt gates unchanged.

Local packet acceptance never promotes a composed row without an independently
accepted caller/child edge certificate. No historical Kani verdict is restored.
"""
from pathlib import Path
import sys,json,hashlib,re,subprocess,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-q-compose-20261029'))
import NEB_validate as neb
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
obj=lambda p:json.loads(p.read_text())
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def require(ok,message):
 if not ok:raise ValueError(message)
def function(text,name):
 m=re.search(r'\bfn '+re.escape(name)+r'\b',text);require(m is not None,'missing function '+name)
 j=text.index('{',m.start())+1;depth=1
 while depth:
  depth+=(text[j]=='{')-(text[j]=='}');j+=1
 return text[m.start():j]
def audit_line(packet):
 require(packet['status']=='CLOSED-CONDITIONAL' and packet['route']=='D188_ACTUAL_BODY_FULL_CALLEES','wrong bridge method')
 require(packet['frozen_revision']==F,'wrong frozen source')
 require(packet['trust_reclassification']=='P6/D188; retained, never removal','wrong trust classification')
 require(packet['new_kani_credits']==[] and packet['suspended_neb_credits_restored']==[],'Kani credit manufactured')
 for item in packet['lean_evidence']:
  for theorem in item['theorems']:neb.check_receipt(item,theorem)
  receipt=obj(R/item['receipt'])
  for path,h in receipt['source_hashes'].items():
   source=R/item['receipt'];archived=source.parent/'sources'/path
   require(sha(archived)==h,'archived proof source')
   current=E/path.removeprefix('NEI_generated/')
   require(current.is_file() and sha(current)==h,'current successful proof source')
 d=obj(E/'NEI_E001/receipt.json');require(d['exit_status']==0 and d['kind']=='extract','actual extraction failed')
 pins=obj(E/'NEI_E001/NEI_EXTRACTION_PINS.json');require(pins['exit']==0 and pins['charon_exit']==0,'translator failure')
 require(pins['lock_before']==pins['lock_after'],'extraction lock drift')
 require('--include' in pins['charon_command'] and 'aspis_core::field' in pins['charon_command'],'field methods left opaque')
 for path,h in pins['outputs'].items():
  require(sha(E/path)==h,'edited raw emitted source')
  direct=E/'NEI_LineFull'/Path(path).name
  require(sha(direct)==h,'working emitted source differs')
  raw=direct.read_text();require(not re.search(r'\b(axiom|sorry|admit|native_decide)\b|FunsExternal|TypesExternal',raw),'opaque or admitted actual-body declaration')
 frozen=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/verifier.rs'],cwd=R).decode()
 body=function(frozen,'line_fold_with_inverses');h=hashlib.sha256(body[body.index('{'):].encode()).hexdigest()
 require(h==packet['source_body_sha256'],'frozen line body hash')
 require(function((E/'NEI_ISOLATED.rs.txt').read_text(),'line_fold_with_inverses')==body,'isolation changed line body')
 require(function((E/'NEI_line_native.rs').read_text(),'line_fold_with_inverses')==body,'native fixture changed line body')
 require(not re.search(r'&mut|static\s+mut|unsafe|copy_from_slice|extend_from_slice|to_vec',body),'unreviewed native effects/copies')
 positive=obj(E/'NEI_N001/receipt.json');negative=obj(E/'NEI_N002/receipt.json')
 require(positive['exit_status']==0 and negative['exit_status']==101,'line fidelity/control verdict')
 require(positive['source_hashes']==negative['source_hashes'],'control source mismatch')
 env=copy.deepcopy(negative['env']);require(env.pop('NEI_WRONG',None)=='1' and env==positive['env'],'control configuration mismatch')
 require('1 passed; 0 failed' in (E/'NEI_N001/stdout.log').read_text(),'positive test not reached')
 require("thread 'NEI_line_differential'" in (E/'NEI_N002/stdout.log').read_text() and 'assertion `left == right` failed' in (E/'NEI_N002/stdout.log').read_text(),'negative did not fail line assertion')
 np=obj(E/'NEI_LINE_NATIVE_PINS.json');require(np['lock_before']==np['lock_after']==pins['lock_after'],'frozen native lock changed')
 require(sorted(np['features'].values(),key=len)==[[],['r0']],'wrong native core feature projection')
 for path,h in np['source_pins'].items():
  require(hashlib.sha256(subprocess.check_output(['git','show',F+':'+path],cwd=R)).hexdigest()==h,'native core source drift')
 review=R/packet['review']['path'];require(sha(review)==packet['review']['sha256'],'association review hash')
 require(packet['remaining_inner_hypotheses']==[],'inner native/model hypothesis hidden')
 return dict(function=packet['function'],status='CLOSED-CONDITIONAL',route=packet['route'],composed_rows_closed=[],kani_credit=0)
def audit_circle(packet):
 require(packet['status']=='CLOSED-CONDITIONAL' and packet['route']=='D188_ACTUAL_BODY_SHARED_CALLEES','wrong shared-callee bridge method')
 require(packet['frozen_revision']==F and packet['new_kani_credits']==[] and packet['suspended_neb_credits_restored']==[],'wrong frozen/credit classification')
 require(packet['shared_actual_callee_packet']=='NEI_LINE_PACKET.json','unreviewed actual callee packet')
 for item in packet['lean_evidence']:
  for theorem in item['theorems']:neb.check_receipt(item,theorem)
  d=obj(R/item['receipt'])
  for path,h in d['source_hashes'].items():require(sha(E/path.removeprefix('NEI_generated/'))==h,'current successful circle source')
 d=obj(E/'NEI_E002/receipt.json');require(d['exit_status']==0 and d['kind']=='extract','circle extraction failed')
 pins=obj(E/'NEI_E002/NEI_EXTRACTION_PINS.json');require(pins['exit']==0 and pins['charon_exit']==0 and pins['lock_before']==pins['lock_after'],'circle extraction/lock failure')
 for path,h in pins['outputs'].items():
  raw=E/(path+'.txt' if path.endswith('_Template.lean') else path)
  require(sha(raw)==h,'edited circle raw output')
  if path.endswith('_Template.lean'):continue
  direct=E/'NEI_CircleShared'/Path(path).name;require(sha(direct)==h,'edited circle working output')
  require(not re.search(r'\b(axiom|sorry|admit|native_decide)\b',direct.read_text()),'admitted circle body')
 expected_type='import NEI_LineFull.Types\nnamespace NEI_CircleShared\nabbrev aspis_core.field.wide_exact.WideExact := NEI_LineFull.aspis_core.field.wide_exact.WideExact\nend NEI_CircleShared\n'
 require((E/'NEI_CircleShared/TypesExternal.lean').read_text()==expected_type,'wrong shared actual type')
 ext='import NEI_CircleShared.Types\nimport NEI_LineFull.Funs\nnamespace NEI_CircleShared\n'
 for m in ['add','sub','mul','mul_m31']:ext+=f'abbrev aspis_core.field.wide_exact.WideExact.{m} := NEI_LineFull.aspis_core.field.wide_exact.WideExact.{m}\n'
 ext+='abbrev aspis_core.field.M31.mul := NEI_LineFull.aspis_core.field.M31.mul\nend NEI_CircleShared\n'
 require((E/'NEI_CircleShared/FunsExternal.lean').read_text()==ext,'wrong shared actual field methods')
 source=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/verifier.rs'],cwd=R).decode()
 body=function(source,'circle_fold_with_inverses');require(hashlib.sha256(body[body.index('{'):].encode()).hexdigest()==packet['source_body_sha256'],'wrong frozen circle body')
 require(function((E/'NEI_ISOLATED.rs.txt').read_text(),'circle_fold_with_inverses')==body and function((E/'NEI_circle_native.rs').read_text(),'circle_fold_with_inverses')==body,'changed isolated/native circle body')
 positive=obj(E/'NEI_N003/receipt.json');negative=obj(E/'NEI_N004/receipt.json')
 require(positive['exit_status']==0 and negative['exit_status']==101 and positive['source_hashes']==negative['source_hashes'],'circle fidelity/control verdict or source')
 env=copy.deepcopy(negative['env']);require(env.pop('NEI_WRONG',None)=='1' and env==positive['env'],'circle control configuration')
 require('1 passed; 0 failed' in (E/'NEI_N003/stdout.log').read_text(),'circle positive test not reached')
 log=(E/'NEI_N004/stdout.log').read_text();require("thread 'NEI_circle_differential'" in log and 'assertion `left == right` failed' in log,'circle negative assertion not reached')
 np=obj(E/'NEI_N004/NEI_NATIVE_PINS.json');require(np['lock_before']==np['lock_after']==pins['lock_after'],'circle frozen lock changed')
 require(sorted(np['features'].values(),key=len)==[[],['r0']],'circle native core features')
 for path,h in np['source_pins'].items():require(hashlib.sha256(subprocess.check_output(['git','show',F+':'+path],cwd=R)).hexdigest()==h,'circle native core drift')
 require(sha(R/packet['review']['path'])==packet['review']['sha256'] and packet['remaining_inner_hypotheses']==[],'circle review/inner hypothesis')
 return dict(function=packet['function'],status='CLOSED-CONDITIONAL',route=packet['route'],composed_rows_closed=[],kani_credit=0)

def main():
 packet=obj(E/'NEI_LINE_PACKET.json');results=[audit_line(packet)]
 if (E/'NEI_CIRCLE_PACKET.json').is_file():results.append(audit_circle(obj(E/'NEI_CIRCLE_PACKET.json')))
 if (E/'NEI_ROW_PACKET.json').is_file():
  import NEI_row_validate
  results.append(NEI_row_validate.audit(E,R,obj(E/'NEI_ROW_PACKET.json'),neb,require,function))
 if (E/'NEI_PUSH_PACKET.json').is_file():
  import NEI_push_validate
  results.append(NEI_push_validate.audit(E,R,obj(E/'NEI_PUSH_PACKET.json'),neb,require,function))
 if (E/'NEI_CTOR_PACKETS.json').is_file():
  import NEI_ctor_validate
  results += [NEI_ctor_validate.audit(E,R,p,neb,require) for p in obj(E/'NEI_CTOR_PACKETS.json')]
 if (E/'NEI_GETTER_PACKETS.json').is_file():
  import NEI_getter_validate
  results += [NEI_getter_validate.audit(E,R,p,neb,require) for p in obj(E/'NEI_GETTER_PACKETS.json')]
 if (E/'NEI_WIDE_CTOR_PACKET.json').is_file():
  import NEI_wide_ctor_validate
  results.append(NEI_wide_ctor_validate.audit(E,R,obj(E/'NEI_WIDE_CTOR_PACKET.json'),neb,require))
 if (E/'NEI_DOT_FINISH_PACKETS.json').is_file():
  import NEI_dot_finish_validate
  results += [NEI_dot_finish_validate.audit(E,R,p,neb,require) for p in obj(E/'NEI_DOT_FINISH_PACKETS.json')]
 if (E/'NEI_FIELD_PACKETS.json').is_file():
  import NEI_field_validate
  results += [NEI_field_validate.audit(p,neb) for p in obj(E/'NEI_FIELD_PACKETS.json')]
 delta=obj(E/'NEI_LEDGER_DELTA.json')
 import NEI_composition as composition
 baseline=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json')
 derived,checked=composition.validate(baseline,obj(E/'NEI_EDGES.json'))
 require(delta['composed_rows_closed']==checked['composed_rows_closed'],'uncertified composed promotion')
 require(derived==obj(E/'NEI_DERIVED_LEDGER.json'),'derived ledger differs from checked certificates')
 tests=obj(E/'NEI_COMPOSE_TESTS_receipt.json')
 require(tests['failed']==0 and tests['passed']==29 and len(tests['tests'])==29 and all(t['status']=='PASS' for t in tests['tests']),'new composition checks missing or failed')
 profiles=obj(E/'NEI_PROFILE_TESTS.json')
 require(profiles['failed']==0 and profiles['passed']==5 and profiles['model_packets']==20 and profiles['checked_and_wrapping_profiles_audited'],'release profile checks missing or failed')
 require(delta['added_local_bridges']==[r['function'] for r in results],'wrong local delta')
 edges=obj(E/'NEI_EDGES.json')['edges']
 require(all((e['status']=='OPEN' and e['certificate'] is None) or (e['status']=='CLOSED' and e['certificate']['id'].startswith('NEI-')) for e in edges),'edge credit without a new NEI certificate')
 require(sha(E.parent/'native-ledger3-20261029/NDT_LEDGER.json')==delta['authoritative_ledger_sha256'],'authoritative ledger changed')
 print(json.dumps(dict(original_neb_receipt_gates='PASS',additive_d188_packets=results,original_checks_retained_verbatim=True,composed_rows_closed=checked['composed_rows_closed']),indent=2))
if __name__=='__main__':main()
