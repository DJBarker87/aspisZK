"""Make the complete pinned child-slot inventory, without inferring closure."""
import collections,json,lzma,pathlib
E=pathlib.Path('evidence/pv-lib-20261107')
rs=json.loads(lzma.decompress((E/'inputs/ledger.xz').read_bytes()))['rows']
rows={r['id']:r for r in rs};providers=json.loads((E/'PROVIDERS.json').read_text())
dep=json.loads((E/'DEPENDENCIES.json').read_text())
instances={}
if (E/'INSTANCES.json').exists(): instances=json.loads((E/'INSTANCES.json').read_text())
slots=[]
for parent in dep['order']:
 r=rows[parent]
 for child in r['callees']:
  c=rows[child];p=providers.get(child);inst=instances.get(child)
  sites=[s['site'] for s in r['call_sites'] if s['row']==child]
  if p:
   namespace=p['theorem'].rsplit('.',1)[0]
   definitions=p.get('definitions_qualified',[namespace+'.'+n for n in p['definitions']])
  else:definitions=[]
  status='INSTANTIATED' if inst and inst.get('compiled') else 'MISSING-CHILD-LEMMA'
  reason=('No CLOSED provider: '+c['status']) if c['status']!='CLOSED' else (
   'CLOSED root retained. Exact deterministic model graph, caller-domain and actual-machine adapter not yet proved in PLIB; no relational law installed.')
  if status=='INSTANTIATED':reason=inst['qualification']
  slots.append(dict(slot=parent+' -> '+child,parent=parent,child=child,sites=sites,
   provider_status=c['status'],root=p,provider_definitions=definitions,
   adapter='Literal provider Input/Pre/value/finalStore/output definitions listed here; SAME emitted operands and current entry state. Graph equality, required-cell frame and numbering; reached-machine transport where specialized. No whole-store/counter equality.',
   status=status,reason=reason,instance=None))
facets=[
 ('thread:OwnInit','decodeBridged14756','SPEC-ERROR','PV_THR2_OwnInitSourceCodec.decodeBridged; PV_THR2_BoxDynRepresentationBridge; PV_THR2_OwnInitActualAllocationOwned.allBridged; SourceInitBoxOwnership','Old decode/all/Shape cannot be used at tagged source14756. Full actual bridge/source/binary adequacy and continuous milestone composition remain missing.'),
 ('slice:f21','actualPending','SPEC-ERROR','PV_STX2_ToVecCallSummary.Pending; PV_STX2_ToVecCallPendingDiagnostic.actual_entry_false_pending','Old pending accepts an ignored native answer on BODY push. Need completed=none and resolver=none recognizer tests.'),
 ('thread:f170','storeAction289','SPEC-ERROR','PV_THR2_SourceStoreInterpreter.step; PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_CellReplace289','Old interpreter cannot write source cell. New step exists; actual caller provenance/path definedness is not yet derived.'),
 ('thread:f15','storeAction93','SPEC-ERROR','PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_RangeNext93','Original-machine full replies do not implement source Range start write.'),
 ('thread:OwnInit','allCases','SPEC-ERROR','OrderedFamiliesEntryOwned\'; next93 Some/None outcome split','The draft ledger Pre mentions Some. Full root spec covers both discriminants and prior stopped outcomes.'),
 ('slice:f0','entryReferenceValidity','MISSING-CHILD-LEMMA','Source7EntryOwned; PV_STX2_ToVecCallReferenceEntry.Pre; PV_STX2_OwnerAllocationReferenceValid.OwnerWellFormed','Foundation-construction caller must discharge registered non-null/aligned typed initialized ranges. No runtime validity premise added.'),
 ('thread:f361','nameValidity','MISSING-CHILD-LEMMA','PV_FN_THREAD_f361NameEntryValidity.Pre\'; PV_FN_THREAD_f361ScopeEntryValidity.Shape','Caller270 supplies actual Builder.name; opaque String representation source/binary adequacy remains explicit.'),
 ('thread:f6','machineTransport','MISSING-CHILD-LEMMA','PV_THR2_RunAgreement.prefix_identity; PV_FN_THREAD_f6Joins.GlobalOriginalTransport','Reached resolver/handler agreement to old CLOSED124/126 specialized machines must be derived.'),
 ('thread:f361','arcCloneValueFrame','MISSING-CHILD-LEMMA','PV_THR2_LibrarySemantics_ArcClone; PV_FN_THREAD_f360.contract_frame; PV_FN_THREAD_f124.contract','PV_LIB_ArcClone360 now reuses the named source semantics and overflow guard. Actual f361 handler/value/frame binding remains missing; the generic graph alone does not discharge this facet.'),
 ('thread:f361','atomicCounts','MISSING-CHILD-LEMMA','PV_THR2_LibrarySemantics_AtomicUsizeNew; PV_FN_THREAD_f121.contract_value; PV_FN_THREAD_f124.contract','PV_LIB_Arc124Counts now joins actual strong=weak=1 exports to the same construction graph. Actual f361 caller binding and retained representation/frame transport remain missing.'),
 ('slice:f7','typedDrop178','MISSING-CHILD-LEMMA','PV_FN_SLICE_f22_TypedDestructor.run; PV_FN_SLICE_f7_DestructorBinding.selected; PV_FN_SLICE_f7_RuntimeDrop.run','W2 typed destructor proof exists; PLIB graph/runtime carrier adapter has not been installed.'),
 ('thread:OwnInit','numbering','MISSING-CHILD-LEMMA','PV_STX2_LiveNumbering.Numbered; initial; push; waiting_mono; stack_mono; caller_older','Reuse existing invariant lemmas by name at actual caller entries; no equality of summary and expanded counters.'),
 ('thread:OwnInit','registryFrame','MISSING-CHILD-LEMMA','PV_THR2_OwnUniformResourceHandler.lift; PV_W1_OwnerWellFormed.OwnerWellFormed','PV_LIB_Registry.certified proves the concrete lift graph and frame on every answer, with prefix-only abort. Binding this builder to the actual OwnInit environment and composing explicit OWNER actions remain missing.'),
 ('thread:OwnInit','resourceEnv','MISSING-CHILD-LEMMA','PSPEC_COMMON.Env; existing Resources/Backend request functions','Site/occurrence indexed reservation/allocation channel is specified; a source-associated concrete environment binding for all leaves is absent.'),
]
for parent,child,status,defs,reason in facets:
 slots.append(dict(slot=parent+' :: '+child,parent=parent,child=child,sites=[],provider_status='FACET',root=None,
  provider_definitions=defs.split('; '),adapter=defs,status=status,reason=reason,instance=None))
counts=dict(collections.Counter(s['status'] for s in slots))
out=dict(schema=1,qualification='Mapping and instances only; no closure or endpoint consumption',
 source_pins='INPUT_REVISIONS.json',closed_ledger_rows=96,total_ledger_rows=125,spec_rows=29,
 dependency_order=dep['order'],cycles=dep['cycles'],joint_premises='NOT PROVED; see TOP_COMPOSITION.md',
 counts=counts,slots=slots)
(E/'PLIB_MAP.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['# PLIB child behavior map','',
 'Target not yet established. Every edge in both root call closures is included, including transitive CLOSED-provider dependencies. Facets follow the edges. CLOSED ledger status is preserved; it does not certify that a graph/value/representation adapter exists.',
 '',f'{len(slots)} slots; status counts: `{counts}`. Syntactic cycles: none. Joint machine/representation premise satisfiability: NOT PROVED.',
 '', 'The JSON is authoritative for exact theorem, branch, revision, source SHA, provider definitions, call sites, adapters and instance receipts. Generic native full-reply Posts are not deterministic child laws. No child law is a relation.',
 '', '| Consumer | Child / facet | Supplier | Status | Adapter / gap |','|---|---|---|---|---|']
for s in slots:
 p=s['root'];supplier=f"`{p['theorem']}` at `{p['revision'][:12]}` ({p['branch']})" if p else 'No CLOSED root for this slot'
 lines.append('| `'+s['parent']+'` | `'+s['child'].replace('|','\\|')+'` | '+supplier+' | '+s['status']+' | '+s['reason']+' |')
lines+=['','## Scope of instances','',
 'An INSTANTIATED entry names a compiled adapter of the cited provider model. Its qualification records whether actual-machine transport and caller-domain discharge remain. Do not interpret a graph scaffold or a copied root name as an instance. MISSING-CHILD-LEMMA means the required export/adapter remains to be proved, including for CLOSED leaves with only an arbitrary full-reply law. SPEC-ERROR identifies a documented mismatch in the old package interface; its normative replacement is in PSPEC and TOP_COMPOSITION. No false domain or fixed-success environment is used.']
(E/'PLIB_MAP.md').write_text('\n'.join(lines)+'\n')
print(len(slots),counts)
