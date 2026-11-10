import json,re,lzma
defs=json.load(open('/tmp/p3o_defs.json')); rows=json.load(open('/tmp/p3o_rows.json'))
dep=json.load(open('PCVO_DEPLOYED_OPS.json'))
full=lzma.open('PCVO_L008/stdout.log.xz','rt').read()
def lib_row(f):
    if f.startswith(('solana_pubkey','solana_program_error','solana_hash','solana_sha256')): return 'HM-A SDK types/functions (Pubkey, ProgramError, Hash, hashv syscall)'
    if f.startswith('core_option') or f.startswith('core_result'): return 'HM-C Option/Result'
    if f.startswith('core_ops_range') or f.startswith('core_slice') or f.startswith('Slice_Insts'): return 'HM-D array/slice (RangeFull SliceIndex, slice first, slice/array PartialEq)'
    return None
out=[]
for key,f,rhs,_ in rows:
    fam={'st':'x','ca':'x'}
    m=re.search(r'ops\.op(\d+)',rhs)
    opn=('op'+m.group(1)) if m else None
    side='adapter' if key in('stage1','stage2') else 'current'
    val=dep[side].get(opn) if opn else None
    lr=lib_row(f)
    # gate-def matches by name
    matches=[]
    mm=re.match(r'@?((?:AdapterRw|AspisR1CurrentCaller)\.[A-Za-z0-9_.]+)',rhs)
    if mm and not opn:
        nm=mm.group(1)
        if nm in defs: matches=[(nm,[(x[1],x[2]) for x in defs[nm]])]
    # identifiers in the deployed value
    ids=[]
    if val:
        for t in re.findall(r'[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)+',val):
            if t in defs: ids.append((t,sorted(set(str(x[1]) for x in defs[t]))))
    if lr: cls='DEPENDS_ON_LIBRARY_TRUST'; why=lr
    elif opn is None and not rhs.startswith('AdapterRw.') and not rhs.startswith('AspisR1CurrentCaller.') and not rhs.startswith('ok (') and not rhs.startswith('@AdapterRw'):
        cls='UNCLASSIFIED'; why=rhs
    elif opn is None:
        cls='GATE_DEFINITION_FIELD' if matches else 'GATE_DEFINITION_NO_PCXD_RECORD'
        why='x field is defined as the gate definition itself (organisation); status is that of the gate definition' if matches else 'x field is defined as the gate definition itself (organisation); PCXD_PROVENANCE has no record for this gate item (statement-crate constant/function), so no fresh=gate theorem is cited'
    else:
        cls='DEPLOYED_SLOT_NOT_RELATED_TO_FROZEN_EMISSION'; why='x field := ops.%s (organisation); the deployed value is an install wrapper/model; no proved equation to the frozen emission of the callee'%opn
    out.append(dict(file=key,ext_field=f,bound_rhs=rhs,deployed_slot=opn,deployed_value=(val or '')[:170],classification=cls,reason=why,gate_def_status=matches[:2],deployed_value_named_items=ids[:4]))
json.dump(dict(schema='PCVO_UNRELATED/1',target_established=False,note='Every x field is defined from the Ops (organisation, not discharge). No callee is claimed related to its frozen emission by this job; per-callee classification and the status of any named gate/deployed item in PCXD_PROVENANCE.json.',items=out),open('PCVO_UNRELATED.json','w'),indent=1,ensure_ascii=False)
from collections import Counter
print(Counter(o['classification'] for o in out))
for o in out:
    if o['classification'] in('UNCLASSIFIED',): print(o['file'],o['ext_field'],o['bound_rhs'])
print(sum(1 for o in out if o['deployed_value_named_items']), 'with named statuses')
