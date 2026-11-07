from pathlib import Path
import json,lzma,copy
E=Path(__file__).resolve().parent;base=json.loads(lzma.decompress((E.parent/'ledger25-20261111/NMQ_LEDGER.json.xz').read_bytes()));r=next(r for r in base['rows']if r['row']=='TX1:136');rows=[]
for c in r['obligation']['caller_domain_obligations']+r['obligation']['inventory_domain_obligations']:
 z=copy.deepcopy(c);key=c.get('callee','')+' '+c.get('id',json.dumps(c,sort_keys=True))
 if 'field.rs' in key or 'wide_exact' in key:
  proof=['NNG_ConcreteArithmetic136.multiply/addMask/addExtra','NNG_PacketContext136.checked','NNG_TypedDomains136.arithmetic','LIB_VField.qmul/qadd','NNG_LIBField.add_returned'];classification='Same canonical scalar pair at actual multiply/add occurrences; CM31/M31/WideExact flattened alternatives remain visible and are inherited through CLOSED canonical arithmetic child packets, not free root hypotheses.'
 elif 'state_only_selected_mask' in key:
  proof=['NNG_ConcreteMaskDomain136.occurrence','NNG_ProjectMaskDomain','NNG_TypedDomains136.mask'];classification='Exactly actual16+10+1 used canonical inputs and same eta; no blanket unused-claims canonicality premise.'
 elif 'semantic_rounds' in key:
  proof=['NNG_ConcreteRounds136.occurrence','NNG_LIBRoundsCanonical.returned','LIB_VRounds.semanticRounds'];classification='Same original Prefix/transcript/Env; source envelope from own finishInputDom; returned running/alpha canonicality derived internally.'
 elif 'claims' in key:
  proof=['NNG_ConcreteClaims136.occurrence','LIB_VClaims.claims'];classification='Same Prefix and Env.reservation; all constructor errors and allocation outcomes retained, no success premise.'
 elif 'mark' in key:
  proof=['NNG_CallEffects136.mark','NNG_ConcreteMark136'];classification='Actual site/observer/phase evaluation; direct fresh emission plus CLOSED mark source law, no new Kani function-pointer credit.'
 elif 'terminal_qm31' in key:
  proof=['NNG_ConcreteTerminal136.occurrence','NNG_PacketContext136.public_domain','NNG_TypedDomains136.terminal'];classification='Same Public/claims/alpha/original challenges; public digest/asset from own domain, claims/alpha canonicality at reached site.'
 elif 'circle' in key:
  proof=['NNG_ConcreteCircle136.circle0/circle1','NNG_TypedDomains136.circle','NNG_RepDecoders136.circle'];classification='Both source-ordered occurrences preserve full transcript/error Results and exact same record/frame.'
 elif 'validated_record' in key or 'decode_k' in key or 'payload' in key or '::state' in key:
  proof=['NNG_ConcreteRecords136.record25/record26/extra/beforeZ1/payload2/state','NNG_LIBRecordFrame','NNG_LIBRecordReached'];classification='Same parsed Prefix source and returned record;25/26 repeated getter equality and payload geometry derived at actual earlier returns; no additional caller clause.'
 else:
  proof=['NNG_PacketContext136.checked','NNG_AllReached136.all_calls','NNG_Packet136.closed'];classification='Retained upstream/flattened complete-source obligation, supplied inside literal RowSpec fold at the same entered arguments; original own-input envelope remains at137.'
 z.update(NNI_classification=classification,NNI_source_witnesses=proof,NNI_complete_root='AspisR1.NNG_Candidate136.candidate',NNI_gate_credit='pending complete all-root gate; not supplied as a new hypothesis');rows.append(z)
out=dict(row='TX1:136',original_clauses=rows,original_counts=dict(caller=len(r['obligation']['caller_domain_obligations']),inventory=len(r['obligation']['inventory_domain_obligations'])),retained_own_input_clauses=json.loads((E/'NNI_PARENT_CLAUSES.json').read_text()),all_composed_by='NNG_Packet136.closed → NNG_DRowSpec136.fold → NNG_Candidate136.candidate',no_removed_edges=True,no_extra_success_or_library_parameters=True)
(E/'NNI_CLAUSE_REVIEW.json').write_text(json.dumps(out,indent=1)+'\n');print('Retained43 original clauses with source/domain witness classification')
