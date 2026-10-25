"""Bounded future admission semantics. Never traverses raw decision subtrees.
No policy authority: reporting failure denies orchestration; unknown is not GO.
"""
import hashlib
import json

LIMIT=65536
BOOLS=('allowed','adopted','cap_ok','available_ok','legacy_nonreserve_gate_ok')
NUMBERS=('additional_bytes','requested_bytes','os_control_bytes','safe_limit_bytes',
         'projected_reserved_bytes','min_mem_available_bytes','max_active_file_bytes',
         'max_kernel_withheld_bytes','max_root_residual_bytes','adjusted_available_bytes',
         'required_bytes','margin_bytes')
TEXT=('schema','phase','error','reason')


def unknown(phase):
    return dict(schema='FinalNativeGate-compact-admission-v5',phase=phase,status='unknown',
                allowed=None,reporting_failed=True,error='decision unavailable; no GO inference')


def project(phase,report):
    """Whitelist concrete evaluate fields, including its signed margin.
    Missing fields stay absent. Oversize/invalid semantics are reporting failures,
    retaining bounded hashes of omitted TEXT only, never hashing hidden raw trees.
    Full report hashes/sizes are supplied separately by existing save receipts.
    """
    out=unknown(phase);faults=[]
    if type(report) is not dict or type(report.get('decision')) is not dict:return out
    decision=report['decision'];selected={}
    def text(value):
        if type(value) is not str:
            faults.append('invalid text');return {'error':'invalid text type'}
        if len(value)<=2048:return value
        h=hashlib.sha256();size=0
        for at in range(0,len(value),4096):
            raw=value[at:at+4096].encode('utf-8');h.update(raw);size+=len(raw)
        faults.append('text omitted:2048 character bound')
        return dict(size=size,sha256=h.hexdigest(),encoding='UTF-8',truncation_error=faults[-1])
    for key in BOOLS:
        if key in decision:
            if type(decision[key]) is bool:selected[key]=decision[key]
            else:faults.append('invalid boolean:'+key)
    for key in NUMBERS:
        if key in decision:
            value=decision[key]
            if type(value) is int and -(2**64-1)<=value<=2**64-1:selected[key]=value
            else:faults.append('invalid numeric budget:'+key)
    if 'expected_limits' in decision:
        limits=decision['expected_limits']
        if limits is None:selected['expected_limits']=None
        elif type(limits) is dict:
            selected['expected_limits']={}
            for key in ('high','cap','swap_max','tasks_max'):
                if key in limits:
                    value=limits[key]
                    if type(value) is int and 0<=value<=2**64-1:selected['expected_limits'][key]=value
                    else:faults.append('invalid expected limit:'+key)
        else:faults.append('invalid expected_limits')
    for key in TEXT:
        if key in decision:selected[key]=text(decision[key])
    for key in ('errors','reasons'):
        if key in decision:
            values=decision[key]
            if type(values) is list and len(values)<=16:selected[key]=[text(v) for v in values]
            else:faults.append('invalid/oversized semantic list:'+key)
    failures=decision.get('collection_failures')
    if failures is not None:
        if type(failures) is not dict:faults.append('invalid collection_failures')
        else:
            selected['collection_failures']={}
            for label in ('visibility','before','after'):
                if label not in failures:continue
                item=failures[label]
                if type(item) is not dict:faults.append('invalid collection failure:'+label);continue
                row={}
                for key in ('error','type','reason'):
                    if key in item:row[key]=text(item[key])
                if 'errno' in item:
                    n=item['errno']
                    if n is None or (type(n) is int and -2**31<=n<2**31):row['errno']=n
                    else:faults.append('invalid errno')
                selected['collection_failures'][label]=row
            if any(k not in ('visibility','before','after') for k in failures):faults.append('unknown collection failure fields omitted')
    if selected.get('allowed') is True and any(k in selected for k in ('error','collection_failures')):
        faults.append('allowed with error/failure semantics; no GO inference')
    if 'allowed' not in selected:faults.append('missing/invalid allowed; unknown')
    out.update(decision=selected,allowed=selected.get('allowed'),
               status='allowed' if selected.get('allowed') is True else 'denied' if selected.get('allowed') is False else 'unknown',
               reporting_failed=bool(faults),errors=faults)
    out.pop('error',None)
    raw=json.dumps(out,sort_keys=True,allow_nan=False).encode()
    if len(raw)>LIMIT:
        return dict(schema=out['schema'],phase=phase,status='reporting_error',allowed=None,
                    reporting_failed=True,size=len(raw),sha256=hashlib.sha256(raw).hexdigest(),
                    truncation_error='compact projection exceeds64KiB; hash-only; no GO inference')
    return out


def receipt(record,rows):
    # Only the three concrete full-report receipts, never another report object.
    selected=[]
    for row in rows:
        if type(row) is not dict:raise ValueError('invalid admission receipt')
        name,size,digest=(row[k] for k in ('name','size','sha256'))
        if type(name) is not str or len(name)>128 or type(size) is not int or size<0 or type(digest) is not str or len(digest)!=64:
            raise ValueError('invalid admission receipt fields')
        selected.append(dict(name=name,size=size,sha256=digest))
        if len(selected)>3:raise ValueError('admission receipt count')
    candidate=dict(record,full_evidence=selected)
    raw=json.dumps(candidate,sort_keys=True,allow_nan=False).encode()
    if len(raw)>LIMIT:
        phase=record['phase'];record.clear()
        record.update(schema='FinalNativeGate-compact-admission-v5',phase=phase,status='reporting_error',
                      allowed=None,reporting_failed=True,size=len(raw),sha256=hashlib.sha256(raw).hexdigest(),
                      truncation_error='compact with receipts exceeds64KiB; hash-only; no GO inference')
        raise ValueError('compact admission64KiB bound')
    record['full_evidence']=selected
