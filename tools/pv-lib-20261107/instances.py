"""Report actual compiled fields. No unproved field is marked installed."""
import json,pathlib
E=pathlib.Path('evidence/pv-lib-20261107')
providers=json.loads((E/'PROVIDERS.json').read_text())
receipts=[json.loads(p.read_text()) for p in E.glob('receipt-*.json')]
by_module={r['target']:r for r in receipts if r['accepted'] and not r['runtime_audit']}
fields={}
def field(row,module,model,law,theorem,qualification):
    r=by_module.get(module)
    fields[row]=dict(module=module,model=model,law=law,theorem=theorem,
        root=providers[row],compiled=bool(r),attempt=r['attempt'] if r else None,
        source_sha256=r['source_sha256'] if r else None,raw_audited=False,
        graph_of_function=True,qualification=qualification)
for n in [12,15,23]:
    field('slice:f'+str(n),'PV_LIB_ArrayInstances','PV_LIB_ArrayInstances.model'+str(n),
        'PV_LIB_ArrayInstances.law'+str(n),'PV_LIB_ArrayInstances.installed'+str(n),
        'Literal CLOSED value/finalStore model; public observation erases abort state and activation counter. Call-entry typed domain/numbering and machine neutrality remain caller discharge, not assumed successes.')
field('slice:f11','PV_LIB_Array11View','PV_LIB_Array11View.model','Equality with model',
    'PV_LIB_Array11View.abort_prefix','Unconditional emitted abort branch, exact event prefix only; no public post-abort state/frame.')
for n in [315,218,222,126]:
    field('thread:f'+str(n),'PV_LIB_ThreadInstances','PV_LIB_ThreadInstances.model'+str(n),
        'PV_LIB_ThreadInstances.law'+str(n),'PV_LIB_ThreadInstances.installed'+str(n),
        'Literal provider deterministic all-answer function; observation graph abstracts counter and abort state. Specialized-machine transport and actual-call Pre discharge remain named consumer obligations; no actual root composition claimed.')
field('thread:f164','PV_LIB_VecNew','PV_FN_THREAD_f164.output followed by PV_LIB.observe',
    'PV_LIB_VecNew.law','PV_LIB_VecNew.installed',
    'CLOSED164 output at actual named268 environment reply, all answers; source selected representation. Original-machine resolver transport remains consumer work.')
field('thread:f216','PV_LIB_Arc216','PV_LIB_Arc216.model','PV_LIB_Arc216.law','PV_LIB_Arc216.installed',
    'Literal CLOSED216 two-call function and every stop; exact public observation. Actual original-machine handler/resolver agreement remains consumer work.')
for n in [217,312,313,320,134,344]:
    field('thread:f'+str(n),'PV_LIB_PureLeaves','PV_LIB_PureLeaves.model'+str(n),
        'PV_LIB_PureLeaves.law'+str(n),'PV_LIB_PureLeaves.certified'+str(n),
        'Graph of literal CLOSED pure-leaf call function, with separate root certificate. Native binding/source representation validity on the actual caller machine remains the named documented-semantics obligation; arbitrary provider Post is not used as law.')
if (E/'RAW_AUDIT.json').exists():
    audit=json.loads((E/'RAW_AUDIT.json').read_text())
    audited={r['root'] for r in audit['roots'] if r['equal']}
    for f in fields.values():
        f['raw_audited']=f['compiled'] and f['theorem'] in audited
        f['audit_attempt']=audit['attempt'] if f['raw_audited'] else None
(E/'INSTANCES.json').write_text(json.dumps(fields,indent=2)+'\n')
print(sum(f['compiled'] for f in fields.values()),'compiled provider fields;',sum(not f['compiled'] for f in fields.values()),'not yet compiled')
