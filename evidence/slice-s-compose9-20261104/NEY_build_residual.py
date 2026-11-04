"""Build residual certificates only after the full positive/control set passes."""
import json
import NEY_validate as v
import NEY_residual_checks as checks
E=v.E;R=v.R

def add(packet,base,theorem,ref):
 configs={checks.BIND:{'positive':'NEY_K109','value':'NEY_K110'},checks.ENC:[[f'NEY_K{111+i*2:03}',f'NEY_K{112+i*2:03}'] for i in range(9)],checks.EMIT:{'positive':'NEY_K129','byte':'NEY_K130','order':'NEY_K131','argument':'NEY_K132'}}
 receipts={'NEY_BindingContinuation':'NEY_L004','NEY_BindingSuccess':'NEY_L007','NEY_ReachedResultDomains':'NEY_L040','NEY_ResultEncoderOracle':'NEY_L008','NEY_ResultStores':'NEY_L038','NEY_ResultProjection':'NEY_L039','NEY_ResultConstants':'NEY_L037','NEY_EmitComposed':'NEY_L041','NEX_ReturnData':'NEX_L014'}
 for f in checks.FUNCTIONS:
  conf=configs[f];attempts=list(conf.values()) if f!=checks.ENC else [a for pair in conf for a in pair]
  if not all((E/a/'receipt.json').exists() for a in attempts):continue
  try:{checks.BIND:checks.binding,checks.ENC:checks.encoder,checks.EMIT:checks.emission}[f](conf)
  except (AssertionError,KeyError,OSError):continue
  view=v.compose(base,packet);by={}
  for row in view['rows']:by.setdefault(row['function'],[]).append(row)
  thms=[]
  for name in checks.THEOREMS[f]:
   prefix=name.rsplit('.',1)[0];a=receipts[prefix];old=prefix.startswith('NEX_')
   thms.append(theorem(name,a,E.parent/'slice-s-compose8-20261104' if old else E,'NEX_' if old else 'NEY_'))
  support={E/'NEY_RESIDUAL_TEMPLATE_PINS.json'}
  for a in attempts:
   names=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-frozen-identity.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEY_native_contracts.patch',a+'-NEY_oracle.patch']
   archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NEY_SOURCE_HISTORY.json';names += [archive+'.xz',archive+'.sha256'];support.update(E/name for name in names)
  if f==checks.EMIT:
   old=E.parent/'slice-s-compose7-20261103'
   for a in ['NEU_K003','NEU_K004']:
    names=[a+'/receipt.json',a+'/stdout.log',a+'.json','NEU_K004-emit.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEU_native_contracts.patch',a+'-NEU_oracle.patch']
    archive=a+'-inputs.json' if (old/(a+'-inputs.json.xz')).exists() else 'NEU_SOURCE_HISTORY.json';names += [archive+'.xz',archive+'.sha256'];support.update(old/name for name in names)
  c=dict(id='NEY_result_path::'+f,kind='root-composition' if f==checks.EMIT else 'member-composition',subject=f,frozen_revision=base['frozen_revision'],native_certificate=dict(function=f,domain=checks.DOMAINS[f],complete=True,config=conf,inner_hypotheses_remaining=[]),domain_theorems=thms,physical_theorems=thms,support=[ref(p) for p in sorted(support)],required_obligations=[o['id'] for row in by[f] for o in row['caller_domain_obligations']],edges=[edge for edge in checks.common.SPEC['internal_edges'] if edge.startswith(f+' -> ')],hypotheses=[f+'.PacketDomain',f+'.PhysicalInterpretation','RuntimePersistence','CompositionTrustOptionA']+(['RuntimeReturnData'] if f==checks.EMIT else []),new_trust_rows=['RuntimeReturnData'] if f==checks.EMIT else [],addition_classification='ADDED runtime trust under ruling(ab)' if f==checks.EMIT else 'none',inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification',call_domain_certificates={})
  c.update({key:True for key in ['exact_callsite','canonical_carrier','same_arguments','same_prestate','same_result','same_ordered_effects','native_frame_complete','callee_domain_established']})
  for edge in c['edges']:
   caller,g=edge.split(' -> ');obs=[o for r in by[f] for o in r['caller_domain_obligations'] if o.get('callee')==g]
   names=list(dict.fromkeys([h for o in obs for h in o['required_named_hypotheses']]+[h['name'] for row in by[g] for h in row['named_hypotheses']]))
   c['call_domain_certificates'][edge]=dict(subject=edge,classification=checks.classify(f,g),selected_callee_claims=list(dict.fromkeys(x for row in by[g] for x in row['selected_claims'])),inner_names_discharged=names,domain_theorems=thms,physical_theorems=thms,inner_hypotheses_remaining=[],same_arguments=True,same_prestate=True,same_result=True,same_ordered_effects=True,canonical_carrier=True,callee_domain_established=True,native_frame_complete=True)
  c['semantic_review_sha256']=v.sha(json.dumps(c,sort_keys=True).encode())
  assert v.certificate(c,f,view)
  packet['NEY_certificates'][f]=c
 return packet
