#!/usr/bin/env python3
"""Additive NEN ledger refresh. Python/Git receipt checks only; no provers.

Unchanged slice validators remain the authority for certificate semantics.
NEO returns only a delta; a return-event observer reads its already-checked
local ledger without altering code, arguments, return value or any gate.
"""
import argparse
import collections
import copy
import hashlib
import json
import lzma
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
E = Path(__file__).resolve().parent
R = E.parent.parent
LANES = [('NEO','slice-q-compose2-20261102'),('NET','slice-q-compose3-20261102'),
         ('NEI','slice-q-mul2-20261101'),('NEM','slice-s-compose5-20261102'),
         ('NEQ','slice-s-compose6-20261102'),('NEU','slice-s-compose7-20261103'),
         ('NEX','slice-s-compose8-20261104')]
for directory in ['ledger4-20261102'] + [d for _, d in LANES]:
    sys.path.insert(0, str(R / 'evidence' / directory))
import NEN_validate as nen
import NEO_validate as neo
import NET_validate as net
import NEM_validate as nem
import NEQ_validate as neq
import NEU_validate as neu
import NEX_validate as nex

require, sha, encode = nen.require, nen.sha, nen.encode
DESIGN = R / nen.ndt.DESIGN
EXTRA_INPUTS = {}
GROUPS = ['roots','members','hypotheses','edges','inventory_edges','externals']


def read(path):
    path = Path(path)
    if path.is_file():
        return json.loads(path.read_bytes())
    compressed = Path(str(path) + '.xz')
    if not compressed.is_file() and path.is_absolute() and path.is_relative_to(R):
        name=str(path.relative_to(R))
        flag=nen.ndt.git('ls-files','-t','--',name).decode()
        require(flag.startswith('S '),'missing materialized input: '+name)
        revision=json.loads((E/'NEZ_SCOPE.json').read_bytes())['source_revision']
        raw=nen.ndt.git('show',revision+':'+name)
        EXTRA_INPUTS[name]=dict(revision=revision,sha256=sha(raw),bytes=len(raw),sparse=True)
        return json.loads(raw)
    raw = lzma.decompress(compressed.read_bytes())
    require(sha(raw) == Path(str(path) + '.sha256').read_text().strip(), 'transport hash: ' + str(path))
    return json.loads(raw)


def check_inputs():
    pins, scope = read(E / 'NEZ_INPUTS.json'), read(E / 'NEZ_SCOPE.json')
    args = [*scope['input_directories'], nen.ndt.DESIGN]
    actual = {}
    for line in nen.ndt.git('ls-tree','-rl','HEAD','--',*args).decode().splitlines():
        meta,path = line.split('\t',1)
        _,kind,oid,size = meta.split()
        if kind == 'blob':
            actual[path] = dict(git_blob=oid,bytes=int(size))
    require(actual == pins['files'], 'input corpus changed; explicit refresh required')
    require(not nen.ndt.git('diff','HEAD','--',*args), 'dirty or deleted materialized inputs')
    return pins


def closed(out):
    return sorted(r['row'] for r in out['rows'] if r['composed_status'] == 'CLOSED')


def capture_neo(base, peer, edges, parsers=None):
    captured = []
    def observe(frame, event, arg):
        if frame.f_code is neo.compose.__code__ and event == 'return' and isinstance(arg, dict):
            captured.append(frame.f_locals['out'])
    previous = sys.getprofile()
    try:
        sys.setprofile(observe)
        delta = neo.compose(base, peer, edges, parsers)
    finally:
        sys.setprofile(previous)
    require(len(captured) == 1, 'NEO checked output observation missing')
    out = captured[0]
    require(len(closed(out)) == delta['total_closed'], 'NEO observed ledger/delta mismatch')
    return out, delta


def apply_net(base, recipes, peer_rows, peer_recipes, edges):
    """Materialize only exact recipes accepted by unchanged NET continuation.

    Caller certificates must cover every conservative inventory edge and every
    external occurrence. No closure from a headline, fixture or bare PASS.
    """
    net.continuation(edges, recipes)
    out = copy.deepcopy(base)
    by = {r['row']: r for r in out['rows']}
    for candidate in peer_rows:
        old = by[candidate['row']]
        require(old['function'] == candidate['function'] and old['frozen_body_sha256'] == candidate['frozen_body_sha256'], 'NET peer identity')
        old.update(copy.deepcopy(candidate))
        old['active_support_receipts'] = []  # new exact recipe selects no historical native credit
        old['NEZ_certificate'] = next(c for c in peer_recipes if c['row'] == old['row'])
        old['NEZ_provider'] = 'NET'
    edge_index = {e['edge']:e for e in edges['edges']}
    for cert in recipes:
        row = by[cert['row']]
        require(row['function'] == cert['function'] and row['frozen_body_sha256'] == cert['frozen_body_sha256'], 'NET frozen row identity')
        require(row['composed_status'] == 'OPEN', 'NET overwrites prior closed recipe')
        require(cert['remaining_inner_hypotheses'] == [] and cert['domain'], 'NET residual inner hypotheses')
        require({'result','state','ordered_effects','native_association'} <= set(cert['parts']), 'NET incomplete result/frame recipe')
        for ob in row['caller_domain_obligations']:
            if 'callee' in ob:
                edge = edge_index[row['function'] + ' -> ' + ob['callee']]
                require(edge['status'] == 'CLOSED' and edge['certificate'], 'NET missing call certificate: ' + ob['id'])
                ob.update(status='CLOSED',discharged_by=edge['certificate']['id'])
            else:
                require(ob['id'] in cert['external_obligations'], 'NET missing external certificate: ' + ob['id'])
                ob.update(status='CLOSED',discharged_by=cert['id'] + ':' + ob['id'])
        row.update(bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',
                   selected_claims=['NET::'+row['function']],open_transitive_dependencies=[],active_support_receipts=[],
                   composed_reason='Unchanged NET complete recipe, every conservative call/external certificate; retained root domain and physical interpretation',
                   NEZ_certificate=cert,NEZ_provider='NET')
        row['claim_ids'] = list(dict.fromkeys(row['claim_ids'] + row['selected_claims']))
        row['named_hypotheses'] = [dict(name='NET::'+row['function']+'.'+kind,statement=cert['domain']+'; '+', '.join(cert['top_hypotheses']),discharged_by=cert['id']) for kind in ['PacketDomain','PhysicalInterpretation']]
        for ob in row['inventory_domain_obligations']:
            ob.update(status='CLOSED',discharged_by=cert['id'])
    return out


def selected_certificates(row, packet):
    f = row['function']
    subjects = {f} | {f+'::'+h['name'] for h in row['named_hypotheses']}
    subjects |= {f+' -> '+o['callee'] if 'callee' in o else o['id'] for o in row['caller_domain_obligations']}
    return {k:c for group in GROUPS for k,c in packet.get(group,{}).items() if k in subjects}


def native_refs(value):
    paths = set(nen.refs(value))
    # Attempt names inside native_pair/copy_pair recipes are scoped by their
    # immutable lane prefix, never inferred from a passing verdict.
    prefixes = dict(LANES + [('NEE','slice-s-compose2-20261029'),('NEL','slice-s-compose4-20261101'),('NEJ','slice-s-compose3-20261101')])
    for text in nen.strings(value):
        if re.fullmatch(r'NE[A-Z]_K\d+',text) and text[:3] in prefixes:
            path = 'evidence/'+prefixes[text[:3]]+'/'+text+'/receipt.json'
            require((R/path).is_file(), 'missing native recipe receipt: '+path)
            paths.add(path)
    for text in nen.strings(value):
        if re.fullmatch(r'evidence/[^/]+/NE[A-Z]_K\d+/receipt.json',text):
            paths.add(text)
    return sorted(p for p in paths if re.search(r'/[A-Z]+_K\d+/receipt.json$',p) and read(R/p).get('kind') == 'kani')


def new_credit(path, inherited):
    if path in inherited and (inherited[path].get('k2_quarantined') or inherited[path]['k3_status'] != 'OPEN'):
        return inherited[path]
    receipt = read(R/path)
    folder = (R/path).parent.parent
    attempt = (R/path).parent.name
    rule = folder/(attempt+'-rule16-check.json')
    check = read(rule) if rule.is_file() else {}
    safe = check.get('no_writable_static') is True or check.get('static_declarations') == []
    archive = folder/(attempt+'_INPUTS.json.xz')
    if not safe and archive.is_file():
        raw = lzma.decompress(archive.read_bytes())
        require(sha(raw) == (folder/(attempt+'_INPUTS.json.sha256')).read_text().split()[0], 'native snapshot transport hash')
        source = json.loads(raw)
        require(set(source) == set(receipt['source_hashes']), 'native snapshot inventory')
        require(all(sha(text.encode()) == receipt['source_hashes'][name] for name,text in source.items()), 'native snapshot source hash')
        code = [text for name,text in source.items() if name.endswith('.rs')]
        safe = bool(code) and all(not re.search(r'\bstatic\s+mut\b|\bstatic\s+\w+\s*:[^;=]*(?:Atomic|UnsafeCell|RefCell|Cell\s*<)',text) for text in code)
    # Q uses receipt-pinned exact source reviews, not a rule16 sidecar.
    # The unchanged Q checkers already verify these original input snapshots.
    if not safe:
        patches = []
        for name,digest in receipt.get('source_hashes',{}).items():
            if not name.endswith(('.patch','.rs','.rs.txt')):
                continue
            candidates = [folder/(attempt+'-'+name), folder/name, folder/attempt/'sources'/name]
            found = next((p for p in candidates if p.is_file() and sha(p.read_bytes()) == digest),None)
            if found:
                patches.append(found.read_text())
        safe = bool(patches) and all(not re.search(r'\bstatic\s+mut\b|\bstatic\s+\w+\s*:[^;=]*(?:Atomic|UnsafeCell|RefCell|Cell\s*<)',p) for p in patches)
    return dict(NEZ_prior_review=copy.deepcopy(inherited.get(path)),receipt=path,k3_status='UNAFFECTED' if safe else 'OPEN',
                k2_quarantined=False,harness=receipt.get('module',receipt.get('target')),
                reason='Unchanged slice native/source/feature/control gates plus NEZ rule16 denial' if safe else 'No complete receipt-pinned rule16 check')


def validate_row(row, certificates, credits, source_only=False):
    reasons = []
    if not certificates:
        reasons.append('Missing complete row/call-domain/hypothesis composition certificate')
    if row['bridge_status'] != 'CLOSED-CONDITIONAL' or not row['selected_claims']:
        reasons.append('Missing conditional bridge or selected claim')
    if row['open_transitive_dependencies']:
        reasons.append('Open transitive dependencies')
    if any(not h['discharged_by'] for h in row['named_hypotheses']):
        reasons.append('Undischarged named hypothesis')
    if any(o['status'] != 'CLOSED' or not o['discharged_by'] for o in row['caller_domain_obligations']):
        reasons.append('Open caller-domain obligation')
    paths = native_refs(certificates)
    if not paths and not source_only:
        reasons.append('No reviewed active native support')
    reasons.extend(nen.support_gate(paths,credits))
    return paths,reasons


RETURN_DATA = dict(id='RuntimeReturnData',medium='trust row',classification='ADDED by C3-BIN ruling (ab), 2026-11-04',
    scope='set_return_data(b) by P; immediate get_return_data in same instruction context with no intervening CPI returns Some((P,b)) exactly; runtime bound applies.',
    native_obligations=['exact model bytes','exact ordered event position','no later set_return_data'],
    pool_obligations=['immediate read after CPI','check program id','no intervening CPI'],
    pool_status='OPEN: separate native Pool association not supplied by this ledger',
    evidence=['docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md'])


def uses_return_data(value):
    pattern = re.compile(r'RuntimeReturnData|NEX_ReturnData|NEX_EmitRuntime|set_return_data|setReturnData|ruling\s*\(?ab\)?',re.I)
    return sorted({s for s in nen.strings(value) if pattern.search(s)})


def true_key(value,key):
    if isinstance(value,dict):return value.get(key) is True or any(true_key(v,key) for v in value.values())
    if isinstance(value,list):return any(true_key(v,key) for v in value)
    return False


def tag_trust(row, certificates):
    uses = uses_return_data(certificates)
    row['NEZ_trust_rows'] = ['RuntimeReturnData'] if uses else []
    row['NEZ_ab_evidence'] = uses
    row['NEZ_rulings_used'] = (['aa'] if true_key(certificates,'box_ruling_aa') else []) + (['ab'] if uses else []) + (['z(1)'] if 'NEO-observer-root:' in str(certificates) else [])
    return bool(uses)


def unify(base, candidates, reported, certificates, credits, source_only=()):
    out = copy.deepcopy(base)
    by = {r['row']:r for r in out['rows']}
    for rid,(lane,candidate) in candidates.items():
        old = by[rid]
        require(old['function'] == candidate['function'] and old['frozen_body_sha256'] == candidate['frozen_body_sha256'], 'candidate frozen identity')
        # Preserve NEN history even when a later slice changes qualifications.
        require(old['row'] == candidate['row'], 'candidate occurrence identity')
        old.update(copy.deepcopy(candidate))
        old['NEZ_provider'] = lane
    for row in out['rows']:
        rid = row['row']
        row['NEZ_reported_closed_by'] = [p for p,ids in reported.items() if rid in ids]
        row['NEZ_rejections'] = []
        certs = certificates.get(rid,[]) if rid in candidates else []
        if row['composed_status'] == 'CLOSED' and rid in candidates:
            support,reasons = validate_row(row,certs,credits,rid in source_only)
            row['active_support_receipts'] = support
            row['k3_status'] = nen.aggregate(credits.get(p,{}).get('k3_status','OPEN') for p in support) if support else 'UNAFFECTED'
            row['NEZ_rejections'] += reasons
            if reasons:
                row['composed_status'] = 'OPEN'
                row['bridge_status'] = 'OPEN'
        elif row['composed_status'] == 'CLOSED':
            require(not nen.support_gate(row['active_support_receipts'],credits), 'blocked NEN support')
        if row['composed_status'] != 'CLOSED' and not row['NEZ_rejections']:
            row['NEZ_rejections'] = ['Missing complete row/call-domain/hypothesis composition certificate']
        tag_trust(row,certs)
    # Propagate denials across the selected certificates, never historical
    # conservative alternatives or unrelated unused support. Any certificate
    # using a denied positive native receipt is denied by validate_row above.
    denied_ids = set()
    for row in out['rows']:
        if row['NEZ_reported_closed_by'] and row['composed_status'] != 'CLOSED':
            denied_ids.update(row['selected_claims'])
    changed = True
    while changed:
        changed = False
        for row in out['rows']:
            if row['composed_status'] != 'CLOSED':continue
            dependent = [o for o in row['caller_domain_obligations'] if set(o.get('callee_claims',[])) & denied_ids]
            if dependent:
                row['composed_status']='OPEN'
                row['NEZ_rejections']=['Selected active callee claim denied: '+o['id'] for o in dependent]
                denied_ids.update(row['selected_claims']);changed=True
    out['coverage'] = nen.coverage(out['rows'])
    out['NEZ_slice_validator_results'] = reported
    out['NEZ_rejected_slice_closures'] = [dict(row=r['row'],function=r['function'],reported_by=r['NEZ_reported_closed_by'],reasons=r['NEZ_rejections']) for r in out['rows'] if r['NEZ_reported_closed_by'] and r['composed_status'] != 'CLOSED']
    out['NEZ_credits'] = sorted(credits.values(),key=lambda c:c['receipt'])
    out['NEZ_certificates'] = certificates
    # NEN trust rows stay intact. RuntimeReturnData is explicitly additive.
    out['trust_rows'] = copy.deepcopy(base['trust_rows']) + [copy.deepcopy(RETURN_DATA)]
    out['NEZ_ab_closed_native_rows'] = [r['row'] for r in out['rows'] if r['composed_status']=='CLOSED' and 'RuntimeReturnData' in r['NEZ_trust_rows']]
    return out


def specialization():
    """Replay adopted z(2) source certificate and all six original mutations."""
    sys.path.insert(0,str(R/'evidence/slice-q-fnptr-20261029'))
    import NEF_FNPTR_SPECIALISATION as spec
    inputs = read(neo.E/'NEO_SPECIALISATION_INPUTS.json')
    receipt = read(neo.E/'NEO_SPECIALISATION_RECEIPT.json')
    require(receipt['exit_status']==0 and receipt['prover_runs']==0,'specialization receipt')
    for name,digest in receipt['input_sha256'].items():
        require(sha(inputs[name].encode())==digest,'specialization committed input hash: '+name)
    for name,digest in receipt['script_sha256'].items():
        require(sha((spec.E/name).read_bytes())==digest,'specialization source hash: '+name)
    src,nodes=spec.inputs();out,tail,direct=spec.build(src,nodes)
    require(json.loads(inputs['NEF_SPECIALISATION_PAYLOAD.json'])=={n:s for n,s in out.items() if s!=src[n]},'specialization payload drift')
    reference=inputs['NEF_static_ref.rs.txt'];checked=spec.check_reference(reference)
    stored=read(neo.E/'NEO_SPECIALISATION_TEST_RESULTS.json')
    require(stored['positive'] and stored['reference']==checked,'specialization statement drift')
    mutations=[('ops.add(aa,bb)','ops.add(bb,aa)'),('ops.inv(norm)','ops.inv(bb)'),('ops.neg(x.b)','ops.neg(x.a)'),('ops.mul(nb,inv_norm)','ops.mul(nb,norm)'),('NEF_CM{a,b}','NEF_CM{a:b,b:a}'),('self.call(2,a,0)','self.call(3,a,0)')]
    for old,new in mutations:
        require(old in reference,'specialization mutation target missing')
        try:spec.check_reference(reference.replace(old,new,1))
        except AssertionError:continue
        raise ValueError('accepted specialization mutation: '+old)
    return dict(source_certificate=checked,mutation_controls_rejected=len(mutations),
        native_rows_closed=[],scope='Adopted z(2) direct fixed-backend edge only; no full inverse/root bridge')


def source_routes(candidates,certificates):
    """Recognize only unchanged checked source proofs with zero native credit.

    This never restores a native receipt. Observer specialization is z(1).
    The two immutable folds use NEI's actual-body, complete-callee D188 route,
    independently replayed by NEI and selected by NET's peer certificate gate.
    """
    source_only=set()
    review=read(R/'evidence/slice-q-mul2-20261101/NEI_FOLD_REVIEW.json')
    routes={r['function']:r['route'] for r in review if r['kani_credit']==0 and r['route'] in {'D188_ACTUAL_BODY_FULL_CALLEES','D188_ACTUAL_BODY_SHARED_CALLEES'}}
    for rid,(lane,row) in candidates.items():
        cert=certificates[rid];recipe=cert.get('recipe',cert)
        if 'NEO-observer-root:' in str(recipe):
            source_only.add(rid);row['NEZ_support_route']='z(1) exact deployed None source certificate; no native pointer credit'
        elif recipe.get('id','').startswith('NEI-fold-root:'):
            require(row['function'] in routes and recipe['function']==row['function'] and recipe['row']==rid,'wrong D188 source route subject')
            require(recipe['frozen_body_sha256']==row['frozen_body_sha256'] and recipe['remaining_inner_hypotheses']==[],'D188 source route body/inner hypotheses')
            require(recipe['native_review']['path']=='evidence/slice-q-mul2-20261101/NEI_FOLD_REVIEW.json','wrong D188 review path')
            require(sha((R/recipe['native_review']['path']).read_bytes())==recipe['native_review']['sha256'],'D188 source review hash')
            require(not native_refs(cert),'D188 route unexpectedly selects native support')
            source_only.add(rid);row['NEZ_support_route']=routes[row['function']]+'; complete frozen-body/source-to-model certificate; zero Kani credit'
        else:row['NEZ_support_route']='Unchanged complete native/source certificate plus active-receipt K-3/K-2 denial'
    return source_only


def build():
    pins = check_inputs()
    z2 = specialization()
    base = neo.baseline()  # exact NEN output/validator/replay pins and denial gates
    frozen = read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json')
    nen.ndt.validate_invariants(frozen)
    nen.ncz.validate_invariants(frozen)
    qpeer=read(neo.E/'NEO_PEER_POSITIVE.json')
    qout,qd = capture_neo(base,qpeer,read(neo.E/'NEO_EDGES.json'))
    require(qd == read(neo.E/'NEO_LEDGER_DELTA.json'),'NEO checked delta drift')
    reported = copy.deepcopy(base['NEN_slice_validator_results'])
    reported['NEN'] = closed(base)
    reported['NEO'] = closed(qout)
    candidates,certificates = {},{}
    for row in qout['rows']:
        if row['composed_status']!='CLOSED' or row['row'] in reported['NEN']:continue
        candidates[row['row']] = ('Q',row)
        certificates[row['row']] = dict(recipe=row.get('NEO_certificate') or next(c for c in qpeer['row_certificates'] if c['row']==row['row']),active_support_receipts=row.get('active_support_receipts',[]))
    recipes,edges = read(net.E/'NET_CERTIFICATES.json'),read(net.E/'NET_EDGES.json')
    import NET_peer_certificates as peer
    peer_rows,peer_recipes,_ = peer.expected(base)
    qout = apply_net(qout,recipes,peer_rows,peer_recipes,edges)
    reported['NET'] = closed(qout)
    for row in qout['rows']:
        if row.get('NEZ_provider') != 'NET':continue
        candidates[row['row']] = ('Q',row)
        certificates[row['row']] = dict(recipe=row['NEZ_certificate'],active_support_receipts=row.get('active_support_receipts',[]))
    # NEI's current merged result is checked, not replaced by archived earlier
    # NEI capsules imported into NEO/NET. Keep its own occurrence list visible.
    command = [sys.executable,str(E/'NEZ_nei_status.py')]
    with (E/'NEZ_NEI_STATUS.log').open('w') as stream:
        rc = subprocess.run(command,cwd=R,stdout=stream,stderr=subprocess.STDOUT)
    require(rc.returncode == 0, 'NEI isolated unchanged status replay failed; see NEZ_NEI_STATUS.log')
    nei_result = json.loads((E/'NEZ_NEI_STATUS.log').read_text().splitlines()[-1])
    reported['NEI'] = nei_result['closed']
    nei_out = read(R/'evidence/slice-q-mul2-20261101/NEI_DERIVED_LEDGER.json')
    nei_calls = read(R/'evidence/slice-q-mul2-20261101/NEI_COMPOSE_EDGES.json')
    nei_recipes = {c['row']:c for c in nei_calls['row_certificates']}
    for row in nei_out['rows']:
        if row['composed_status']!='CLOSED' or row['row'] in candidates or row['row'] in reported['NEN']:continue
        candidates[row['row']] = ('Q',row)
        packets = []
        for path in (R/'evidence/slice-q-mul2-20261101').glob('NEI_*PACKET*.json'):
            value=read(path)
            packets.extend(c for c in (value if isinstance(value,list) else [value]) if isinstance(c,dict) and c.get('function')==row['function'])
        certificates[row['row']] = dict(recipe=nei_recipes[row['row']],packets=packets)
    for module in [nem,neq,neu,nex]:
        prefix = module.__name__[:3]
        packet = read(module.E/(prefix+'_LEDGER_DELTA.json'))
        review = read(module.E/(prefix+'_REVIEWED_CERTIFICATES.json'))
        checked = module.compose(frozen,packet,review)
        reported[prefix] = closed(checked)
        # Latest layer supersedes only with a fully CLOSED row. Missing later
        # certificates do not erase independently checked earlier alternatives.
        for row in checked['rows']:
            if row['composed_status']!='CLOSED' or row['function'] not in neo.SLICES['S']['functions']:continue
            candidates[row['row']] = ('S',row)
            certificates[row['row']] = selected_certificates(row,packet)
    credits = {c['receipt']:copy.deepcopy(c) for c in base['NEN_credits']}
    diagnostic=dict(candidates=candidates,certificates=certificates,reported=reported)
    packed=lzma.compress(encode(diagnostic).encode(),preset=6)
    (E/'NEZ_CHECKED_CANDIDATES.json.xz').write_bytes(packed)
    (E/'NEZ_CHECKED_CANDIDATES.json.sha256').write_text(sha(lzma.decompress(packed))+'\n')
    paths = native_refs(certificates)
    for path in paths:credits[path] = new_credit(path,credits)
    source_only = source_routes(candidates,certificates)
    out = unify(base,candidates,reported,certificates,credits,source_only)
    out['NEZ_claims'] = {claim:dict(claim_id=claim,
        functions=sorted({r['function'] for r in out['rows'] if claim in r['selected_claims']}),
        rows=[r['row'] for r in out['rows'] if claim in r['selected_claims']],
        composed_rows=[r['row'] for r in out['rows'] if claim in r['selected_claims'] and r['composed_status']=='CLOSED'],
        certificates=[rid for rid in certificates if claim in next(r for r in out['rows'] if r['row']==rid)['selected_claims']],
        qualification='Exact complete statement, domains, frame, source and receipt pins are in NEZ_certificates; inherited claims remain in claims')
        for claim in sorted({c for r in out['rows'] for c in r['selected_claims']})}
    out['NEZ_source_revision'] = pins['revision']
    out['NEZ_baseline'] = dict(path='evidence/ledger4-20261102/NEN_LEDGER.json',sha256=neo.BASE_SHA,
        policy='Exact NEN final outputs, validator sources and exit-0 replay pins reused; unchanged NDT/NCZ structural invariants checked; unchanged current slice certificate gates execute.')
    out['NEZ_budget'] = dict(lean_runs=0,kani_runs=0,native_builds=0,python_aggregate_rss_limit_bytes=nen.CAP)
    slices = neo.SLICES
    out['NEZ_historical_fields'] = 'NEN_* fields retain the historical NEN audit; NEZ_* records govern current admission and rejections.'
    out['NEZ_composed_per_slice'] = {lane:sum(r['composed_status']=='CLOSED' and (candidates.get(r['row'],(r.get('NEN_slice'),))[0])==lane for r in out['rows']) for lane in ['Q','S']}
    out['NEZ_slice_membership'] = {lane:dict(occurrences=sum(r['composed_status']=='CLOSED' and r['function'] in slices[lane]['functions'] for r in out['rows']),
        unique_functions=len({r['function'] for r in out['rows'] if r['composed_status']=='CLOSED' and r['function'] in slices[lane]['functions']})) for lane in ['Q','S']}
    out['NEZ_roots'] = {lane:[dict(function=f,status='CLOSED' if all(r['composed_status']=='CLOSED' for r in out['rows'] if r['function']==f) else 'OPEN',rows=[r['row'] for r in out['rows'] if r['function']==f]) for f in slices[lane]['roots']] for lane in ['Q','S']}
    out['NEZ_z2_status'] = z2
    out['NEZ_per_function'] = {f:dict(rows=[r['row'] for r in out['rows'] if r['function']==f],
        closed=sum(r['composed_status']=='CLOSED' for r in out['rows'] if r['function']==f),
        status='CLOSED' if all(r['composed_status']=='CLOSED' for r in out['rows'] if r['function']==f) else 'OPEN') for f in sorted({r['function'] for r in out['rows']})}
    out['NEZ_slice_per_tx'] = {lane:{tx:sum(r['composed_status']=='CLOSED' and r['function'] in slices[lane]['functions'] and r['row'].startswith(tx+':') for r in out['rows']) for tx in ['TX1','TX2']} for lane in ['Q','S']}
    out['NEZ_validator_coverage'] = {prefix:dict(all_closed=len(ids),Q=sum(r['row'] in ids and r['function'] in slices['Q']['functions'] for r in out['rows']),S=sum(r['row'] in ids and r['function'] in slices['S']['functions'] for r in out['rows'])) for prefix,ids in reported.items()}
    out['NEZ_slice_dispositions'] = {prefix:dict(validator='evidence/'+directory+'/'+prefix+'_validate.py',
        handoff='evidence/'+directory+'/'+prefix+'_HANDOFF.md',
        handoff_sha256=sha((R/'evidence'/directory/(prefix+'_HANDOFF.md')).read_bytes()),
        checked_composed_rows=reported[prefix],
        qualification='Only unchanged complete certificate gates add composition; partial/local/native-window work remains support, never root credit') for prefix,directory in LANES}
    out['NEZ_rulings'] = dict(z1='Deployed cfg-constant None, phase argument order retained; unit/no writes/events/panic/divergence only; historical K-2 unchanged',
        z2='Direct CM31::inv -> CM31::inv_with(M31::inv) only; seven-operation opaque log; field multiplication Lean, M31::neg boundary retained; generic backend excluded',
        aa='Safe Box: existing Allocator trust; same value, same fresh allocation, exact error cleanup; unsafe/MaybeUninit remains ruling b/P6',ab=RETURN_DATA)
    # Enumerate every model-support use separately, including individual
    # theorem statements, rather than count an entire module as a native use.
    model_uses = []
    for name,attempt in [('NEX_ReturnData','NEX_L014'),('NEX_EmitRuntime','NEX_L039')]:
        source = nex.E/(name+'.lean')
        receipt = read(nex.E/attempt/'receipt.json')
        require(receipt['exit_status']==0 and int(receipt['swaps'])==0,'return-data supporting model receipt')
        require(sha(source.read_bytes()) in receipt['source_hashes'].values(),'return-data source receipt pin')
        for audit in receipt['print_axioms']:
            axes=re.search(r'axioms: \[([^]]*)\]',audit)
            require('does not depend on any axioms' in audit or (axes and {x.strip() for x in axes[1].split(',')} <= {'propext','Classical.choice','Quot.sound'}),'return-data unapproved axioms')
        for match in re.finditer(r'^theorem\s+(\w+)',source.read_text(),re.M):
            theorem = name+'.'+match[1]
            require(any("'"+theorem+"'" in a for a in receipt['print_axioms']),'missing return-data axioms status: '+theorem)
            model_uses.append(dict(theorem=theorem,source=str(source.relative_to(R)),source_sha256=sha(source.read_bytes()),receipt=str((nex.E/attempt/'receipt.json').relative_to(R)),trust_rows=['RuntimeReturnData'],classification='MODEL SUPPORT ONLY; native BindingBridge/EncoderBridge remain OPEN'))
    for row in out['rows']:
        if row['function'].endswith('::emit_result'):
            row['NEZ_model_support'] = model_uses
            tag_trust(row,model_uses)
            require(row['composed_status']=='OPEN', 'emit_result native closure requires full child/effect certificate')
    out['NEZ_ab_open_support_rows'] = [r['row'] for r in out['rows'] if r['composed_status']=='OPEN' and 'RuntimeReturnData' in r['NEZ_trust_rows']]
    out['NEZ_ab_uses'] = dict(model_support=model_uses,model_theorem_count=len(model_uses),closed_native_rows=out['NEZ_ab_closed_native_rows'],closed_native_count=len(out['NEZ_ab_closed_native_rows']),open_support_rows=out['NEZ_ab_open_support_rows'],
        closed_roots=[r['function'] for roots in out['NEZ_roots'].values() for r in roots if r['status']=='CLOSED' and set(r['rows']) & set(out['NEZ_ab_closed_native_rows'])],
        pool_status=RETURN_DATA['pool_status'])
    out['status_semantics']['composed_status'] += ' NEZ: unchanged merged slice gates, explicit row recipes, receipt-pinned native denial, per-use trust inventory; no new prover replay.'
    out['critical_path']['status'] = 'Historical NDT advisory frontier only; not recomputed for NEZ'
    out['NEZ_extra_sparse_inputs'] = dict(EXTRA_INPUTS)
    return out


def markdown(d):
    lines = ['# NEZ authoritative ledger','','Target not yet established. Frozen source `'+d['frozen_revision']+'`.','',
        'NEN history is retained. Unchanged slice validators check actual certificates, call domains, full Result/carrier/state/ordered effects, review hashes, controls, features and K-3/K-2. No Lean or Kani ran. Rulings (z)/(aa) retain existing trust; (ab) ADDS RuntimeReturnData.','',
        '| Coverage | Total | CLOSED | OPEN |','|---|---:|---:|---:|']
    for label in ['TX1','TX2','all_rows','unique_functions']:
        c=d['coverage'][label];lines.append(f"| {label} | {c.get('rows',c.get('count'))} | {c['composed_status'].get('CLOSED',0)} | {c['composed_status'].get('OPEN',0)} |")
    lines += ['', 'Contributing slice occurrences: '+str(d['NEZ_composed_per_slice'])+'. Overlapping membership: '+str(d['NEZ_slice_membership'])+'. Shared Q/S to_limbs counted once globally.','', '## Roots','']
    for lane,roots in d['NEZ_roots'].items():
        for root in roots:lines.append('- '+lane+' `'+root['function']+'`: '+root['status']+' ('+', '.join(root['rows'])+').')
    lines += ['', 'Slice membership by TX: '+str(d['NEZ_slice_per_tx'])+'.', '', '## Slice closure reconciliation','', 'Actual validator CLOSED counts: '+', '.join(k+': '+str(len(ids)) for k,ids in d['NEZ_slice_validator_results'].items())+'.', '',
        'NEO/NET counts include inherited global rows; S continuations report their S rows. Full per-slice validator counts are in NEZ_validator_coverage. Rejected slice-reported CLOSED rows: '+str(len(d['NEZ_rejected_slice_closures']))+'.']
    for r in d['NEZ_rejected_slice_closures']:lines.append('- '+r['row']+' `'+r['function']+'`, reported by '+', '.join(r['reported_by'])+': '+'; '.join(r['reasons']))
    lines += ['', '## RuntimeReturnData additions and uses','', 'RuntimeReturnData is ADDED platform trust. Pool immediate read, program-id and instruction-context association remains a separate OPEN obligation.', '',
        f"Model theorem uses: {d['NEZ_ab_uses']['model_theorem_count']}; CLOSED native occurrences: {d['NEZ_ab_uses']['closed_native_count']}; CLOSED roots using (ab): {len(d['NEZ_ab_uses']['closed_roots'])}."]
    for use in d['NEZ_ab_uses']['model_support']:lines.append('- `'+use['theorem']+'` → RuntimeReturnData; '+use['classification']+'. Receipt `'+use['receipt']+'`.')
    lines += ['', '## Occurrence admission and rejection reasons','', '| Row | Function | Composed | Provider | Trust additions | Reason |','|---|---|---|---|---|---|']
    for row in d['rows']:
        reason='All unchanged certificate gates plus unified denial gates accepted' if row['composed_status']=='CLOSED' else '; '.join(row['NEZ_rejections'])
        lines.append(f"| {row['row']} | {row['function']} | {row['composed_status']} | {row.get('NEZ_provider',row.get('NEN_slice',''))} | {', '.join(row['NEZ_trust_rows'])} | {reason} |")
    return '\n'.join(lines)+'\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=build()
    artifacts={'NEZ_LEDGER.json':encode(result).encode(),'NEZ_LEDGER.md':markdown(result).encode()}
    for name,raw in artifacts.items():
        path=E/name
        if len(raw)>20_000_000:
            if args.write:
                Path(str(path)+'.xz').write_bytes(lzma.compress(raw,preset=6))
                Path(str(path)+'.sha256').write_text(sha(raw)+'\n')
            else:
                require(lzma.decompress(Path(str(path)+'.xz').read_bytes())==raw,'derived compressed output drift: '+name)
                require(Path(str(path)+'.sha256').read_text().strip()==sha(raw),'derived hash drift: '+name)
        elif args.write:path.write_bytes(raw)
        else:require(path.read_bytes()==raw,'derived output drift: '+name)
    if args.write:
        require(encode(read(E/'NEZ_LEDGER.json')).encode()==artifacts['NEZ_LEDGER.json'],'written ledger round-trip')
        require((E/'NEZ_LEDGER.md').read_bytes()==artifacts['NEZ_LEDGER.md'],'written markdown round-trip')
    print(json.dumps(dict(coverage=result['coverage'],slices=result['NEZ_slice_membership'],roots=result['NEZ_roots'],rejected=result['NEZ_rejected_slice_closures'],ab=result['NEZ_ab_uses']),indent=2))

if __name__=='__main__':main()
