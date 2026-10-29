"""Explicit current-head review atop the unchanged NDK reconstruction gates.
Python checks evidence consistency; statement/carrier association is an audited
semantic review, not a replacement theorem prover. Never launches proof tools.
"""
import collections
import copy
import hashlib
import io
import json
import lzma
from pathlib import Path
import re
import sys
import tarfile
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent
sys.path.insert(0,str(HERE.parent/'native-ledger2-20261028'))
import NDK_review as legacy
sha=legacy.sha
OLD='evidence/native-ledger2-20261028/'
BASE=json.loads((HERE/'NDT_SCOPE.json').read_text())['research_head']
FROZEN='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'


def check_features(g,scope):
    """Accept complete isolated metadata as well as full workspace records.

    NDE's isolated deployed library graph has six crates, not 441 workspace
    packages. Its generator enumerates EVERY isolated metadata package; the
    over-unified workspace features are never used as deployed parity.
    """
    assert g['graph_matches_frozen'] and not g['edge_errors']
    assert not g['new_package_tuples'] and g['lock_sha256']==legacy.LOCK
    allfs=g.get('resolved_features_all_crates',g.get('all_crate_features'))
    isolated=g.get('isolated_deployed_features')
    assert allfs or isolated,'missing resolved feature listing'
    def mapping(rows):
        return {k:set(v) for k,v in rows.items()} if isinstance(rows,dict) else {r['name']:set(r['features']) for r in rows}
    fs=mapping(isolated or allfs)
    assert {'r0'}<=fs['aspis-core']
    assert {'r0','pool-v1-kernel'}<=fs['aspis-statement']
    audits={f for f in fs['aspis-statement'] if f.endswith('-audit')}
    assert audits==legacy.OPTIMIZED,'wrong optimized expansion'
    assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=fs['aspis-r1-cost-probe']
    if not isolated:assert len(allfs)>=400,'incomplete workspace feature list'
    else:
        assert g['workspace_features_are_overunified'] is True
        assert len(isolated)==6 and set(fs)=={'aspis-core','aspis-statement','aspis-r1-cost-probe','aspis-r0-writer-copies','aspis-r0-block-writer-copies','aspis-r0-poseidon-copy'}
        assert g.get('native_feature_selection'),'no actual native feature selection'
    reached=mapping(g['selected_closure'])
    if scope=='program':
        assert {'pool-adapter','private-leaf-salts'}<=reached['aspis-r1-cost-probe-program']
        assert 'no-entrypoint' not in reached['aspis-r1-cost-probe-program']
    else:assert scope in ['core-helper','library-helper','statement-helper']
    return dict(scope=scope,all_crates_recorded=len(isolated or allfs),feature_record_kind='complete isolated deployed metadata' if isolated else 'all workspace crates',statement_optimized_features=sorted(audits),reached_project_features={k:sorted(v) for k,v in fs.items() if k.startswith('aspis-')})


def restore_patch(raw,base):
    """Apply unified hunks in memory with exact original-context checks."""
    lines=raw.decode().splitlines(keepends=True);out={};i=0
    while i<len(lines):
        if not lines[i].startswith('--- '):i+=1;continue
        old=lines[i][4:].strip();new=lines[i+1][4:].strip();i+=2
        path=new.removeprefix('b/');original=[] if old=='/dev/null' else base(old.removeprefix('a/')).decode().splitlines(keepends=True)
        result=[];pos=0
        while i<len(lines) and not lines[i].startswith('--- '):
            if not lines[i].startswith('@@ '):i+=1;continue
            match=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i]);assert match
            start=int(match[1]);count=int(match[2] or '1');target=start-1 if count else start
            assert target>=pos
            result.extend(original[pos:target]);pos=target;i+=1
            while i<len(lines) and not lines[i].startswith(('@@ ','--- ')):
                line=lines[i];i+=1
                if line.startswith('\\ No newline'):continue
                assert line[:1] in [' ','+','-'],repr(line)
                if line[0] in ' -':assert original[pos]==line[1:],('patch context mismatch',path,pos);pos+=1
                if line[0] in ' +':result.append(line[1:])
        result.extend(original[pos:]);out[path]=''.join(result).encode()
    return out


class Review:
    def __init__(self,s):
        self.s=s;self.archives={};self.patches={};self.theorem_index=None;self.module_index=collections.defaultdict(list)
    def read_snapshot(self,directory,attempt,src,h):
        s=self.s;q=directory+attempt+'/sources/'+src
        if q in s.tree:b=s.read(q);pin=q
        elif directory.endswith('native-front1b-20261028/') and src.endswith('.rs'):
            if directory not in self.archives:
                p=directory+'NDL_SOURCE_ARCHIVE.json.xz';raw=lzma.decompress(s.read(p));assert sha(raw)==s.text(directory+'NDL_SOURCE_ARCHIVE.json.sha256').split()[0]
                self.archives[directory]=json.loads(raw)['source_files']
            entry=self.archives[directory][attempt+'/sources/'+src];assert entry['sha256']==h
            pin=directory+entry['patch'];raw=s.read(pin)
            b=restore_patch(raw,lambda p:b'')[Path(src).name]
        elif directory.endswith('native-front3b-20261028/'):
            if directory not in self.archives:
                index=s.obj(directory+'NDI_RECEIPT_SOURCE_ARCHIVE.json');p=directory+index['archive'];raw=s.read(p);assert sha(raw)==index['archive_sha256']
                unpacked=lzma.decompress(raw);assert sha(unpacked)==index['uncompressed_sha256']
                with tarfile.open(fileobj=io.BytesIO(unpacked),mode='r:') as t:
                    self.archives[directory]={m.name:t.extractfile(m).read() for m in t if m.isfile()}
            key=attempt+'/sources/'+src
            b=self.archives[directory][key];pin=directory+'NDI_receipt_sources.tar.xz'
        elif directory.endswith(('native-front4b-20261028/','native-front5-20261028/')) and src.endswith('.rs'):
            prefix=attempt.split('_')[0]
            pin=directory+attempt+'/'+prefix+'_harness.patch'
            if pin not in self.patches:self.patches[pin]=restore_patch(s.read(pin),lambda p:s.blob(FROZEN+':'+p))
            b=self.patches[pin][src.removeprefix(prefix+'_src/')]
        elif src.endswith('Cargo.lock'):
            b=s.blob(FROZEN+':Cargo.lock');pin='frozen:'+FROZEN+':Cargo.lock'
        elif not src.endswith(('.rs','.lean')):
            # Ancillary controller/config hashes remain in the immutable receipt.
            # They are not claimed recovered if no archived copy exists.
            return dict(source=src,sha256=h,recovered=False,role='ancillary receipt input, no native/theorem body')
        else:raise ValueError('missing selected source snapshot: '+q)
        assert sha(b)==h,('snapshot hash mismatch',q,pin)
        return dict(source=src,sha256=h,recovered=True,pin=pin)
    def theorem(self,name):
        s=self.s
        if self.theorem_index is None:
            self.theorem_index=collections.defaultdict(list)
            # Index focused receipts once; final audits do not replace the source
            # snapshot of the module that actually defines the theorem.
            for p in s.tree:
                if re.search(r'/ND[DEFGHILMN]_L\d+/receipt.json$',p):
                    r=json.loads(s.read(p,cite=False))
                    if r['exit_status']==0:
                        for src,h in r['source_hashes'].items():
                            if src.endswith('.lean'):self.module_index[(Path(src).name,h)].append((p,r,src))
                    if r['exit_status']==0 and isinstance(r.get('print_axioms'),list):
                        for line in r['print_axioms']:
                            match=re.match(r"'([^']+)'",line)
                            if match:self.theorem_index[match[1]].append((p,r))
        mod=name.split('.')[0]
        candidates=[]
        for p,r in self.theorem_index[name]:
            for src,h in r['source_hashes'].items():
                if Path(src).name==mod+'.lean':candidates.append((p,r,src,h))
        for p,r,src,h in sorted(candidates,reverse=True):
            directory=p.split('/'+p.split('/')[-2]+'/')[0]+'/'
            current=directory+mod+'.lean';q=p.removesuffix('receipt.json')+'sources/'+src
            if current in s.tree and q in s.tree and sha(s.read(current))==h:
                archived=s.read(q);assert sha(archived)==h
                legacy.check_theorem(r,name,archived,s.read(current))
                s.read(p);log=p.removesuffix('receipt.json')+'stdout.log';s.read(log)
                return dict(name=name,source=current,source_sha256=h,receipt=p,source_snapshot=q,local_import_sources=self.dependencies(current))
        raise ValueError('no successful matching source/audit: '+name)
    def dependencies(self,path):
        """Pin the transitive local reference/stub/induction sources and their
        matching successful source receipts. Coherent inherited cache imports
        remain reused, with their dependency fingerprints in those receipts.
        """
        s=self.s;seen=set();result=[]
        dirs={'NDD':'native-front1','NDF':'native-front3','NDG':'native-front4','NDE':'native-front2','NDL':'native-front1b','NDN':'native-front2b','NDI':'native-front3b','NDH':'native-front5','NDM':'native-front4b'}
        def walk(p):
            if p in seen:return
            seen.add(p)
            for module in re.findall(r'(?m)^import\s+(\S+)',s.text(p)):
                pre=module.split('_')[0]
                if pre not in dirs:continue
                q='evidence/'+dirs[pre]+'-20261028/'+module.replace('.','/')+'.lean'
                assert q in s.tree,('missing local imported source',q)
                raw=s.read(q);h=sha(raw)
                matches=self.module_index[(Path(q).name,h)]
                assert matches,('no successful receipt for imported source',q)
                receipt,r,src=sorted(matches,key=lambda x:x[0])[-1]
                archived=receipt.removesuffix('receipt.json')+'sources/'+src
                assert s.read(archived)==raw,('local import archive mismatch',q)
                s.read(receipt)
                assert not any('sorryAx' in str(line) for line in r.get('print_axioms',[]))
                if q not in {x['source'] for x in result}:result.append(dict(source=q,sha256=h,receipt=receipt,source_snapshot=archived))
                walk(q)
        walk(path)
        return sorted(result,key=lambda x:x['source'])

    def native(self,directory,item,scope):
        s=self.s;a=item['attempt'];p=directory+a+'/receipt.json';r=s.obj(p);log=s.text(directory+a+'/stdout.log')
        legacy.check_native(r,log,item['positive'])
        g=s.obj(directory+a+'-graph-check.json');features=check_features(g,scope)
        command=r['native_command'];manifest=command[command.index('--manifest-path')+1]
        expected={'program':'programs/r1-cost-probe/Cargo.toml','core-helper':'crates/aspis-core/Cargo.toml','library-helper':'crates/aspis-r1-cost-probe/Cargo.toml','statement-helper':'crates/aspis-statement/Cargo.toml'}[scope]
        assert manifest.endswith(expected),('native root association',a,manifest,scope)
        if g.get('native_feature_selection'):assert command[command.index('--features')+1]==g['native_feature_selection']
        lock=s.obj(directory+a+'-lock-check.json');assert lock['unchanged'] and lock['before']==lock['after']==legacy.LOCK
        assert not s.obj(directory+a+'-source-check.json')['errors']
        snaps=[self.read_snapshot(directory,a,src,h) for src,h in r['source_hashes'].items()]
        return dict(attempt=a,receipt=p,positive=item['positive'],**features,source_snapshots=snaps)


def refresh_claims(s,functions,claims):
    inherited=legacy.refresh_claims(s,functions,claims)
    before=s.obj(OLD+'NDK_LEDGER.json')
    for p in ['NDK_validate.py','NDK_review.py','NDK_tests.py','NDK_ASSOCIATIONS.json']:s.read(OLD+p)
    audit=Review(s);decisions=[]
    specs=json.loads((HERE/'NDT_ASSOCIATIONS.json').read_text())
    for spec in specs:
        directory='evidence/'+spec['packet']+'/'
        if spec['delta_key'] is None:
            matrix=s.text(spec['delta']);assert spec['remaining'] in matrix
            row=dict(function=spec['reported_function'],status='OPEN',obstacle=spec['remaining'])
        else:
            row=s.obj(spec['delta'])[spec['delta_key']][spec['index']]
            assert (row if isinstance(row,str) else row['function'])==spec['reported_function']
        assert spec['function'] in functions,spec['function']
        ev=sorted(p for p in s.tree if p.startswith(directory) and '/' not in p[len(directory):] and (p.endswith('.md') or any(x in Path(p).name for x in ['SOURCE_ASSOCIATION','SOURCE_AUDIT','FINAL_AUDIT','FINAL_SUMMARY','ZERO_ERASURE','REFERENCE_REUSE','FINAL_RESULT','EXTRACTION_PINS'])) and s.tree[p][1]<2*1024*1024)
        for p in ev:s.read(p)
        decision=dict(claim_id=spec['id'],function=spec['function'],decision=spec['disposition'],domain=spec['domain'],reason=spec['remaining'],evidence=spec['delta'])
        decisions.append(decision)
        if not spec['admit']:continue
        assert isinstance(row,dict) and row.get('status',row.get('after')) in ['CLOSED','CLOSED-local','CLOSED-CONDITIONAL']
        assert spec['domain']==row['domain'] and spec['rule14_dependency_audit']
        checks=[audit.native(directory,x,spec['feature_scope']) for x in spec['native']]
        assert any(x['positive'] for x in checks) and any(not x['positive'] for x in checks)
        th=[audit.theorem(t) for t in spec['theorems']]
        rs=[x['receipt'] for x in checks+th]
        ev+=rs+[x['source'] for x in th]+[x['source_snapshot'] for x in th]
        cid=spec['id']
        conditions=[dict(name=cid+'.PacketDomain',statement=spec['domain'],discharged_by=None),dict(name=cid+'.PhysicalInterpretation',statement='Same live native/cohort carrier, installed dictionary and exact source-call/loop association under approved P6/D188 transport; ABI/std/allocator/compiler/source-to-ELF and all enclosing call edges retained. '+spec['remaining'],discharged_by=None)]
        if any(w in spec['function'] for w in ['digest','leaf_hash','Transcript','parent_with']):
            conditions.append(dict(name=cid+'.StaticBackend',statement='Static backend only, no LegacyHashFn/Option<fn> observation; actual digest byte/reply and RuntimeSha256Value interpretation retained.',discharged_by=None))
        c=dict(claim_id=cid,audit_id=cid,function=spec['function'],reported_status=row.get('status',row.get('after')),medium='Controlled native local cuts + pinned safe reference/extraction + exact cohort Lean equation',feature_parity='DEPLOYED selected helper/program features; complete resolved metadata checked',profile=spec['feature_scope'],source_claim_text=row,evidence=sorted(set(ev)),receipts=sorted(set(rs)),quarantined_support=[],replaced_quarantined_support=[],stub_attributes=[],arithmetic_stubs=[],admissible_local_credit=True,limitations=[spec['remaining']],named_hypotheses=conditions,composition_trust='P6/D188 reclassification, not discharge',theorem_associations=th,native_feature_checks=checks,rule14_dependency_audit=spec['rule14_dependency_audit'],delta_row=row)
        claims.setdefault(spec['function'],[]).append(c)
    packets=legacy.review_packets(s)+review_new_packets(s,audit)
    source_associations(s,functions)
    inherited.update(previous_snapshot_revision=before['baseline_revision'],previous_coverage=before['coverage'],previous_frontier_size=len(before['critical_path']['frontier']),associations_sha256=sha((HERE/'NDT_ASSOCIATIONS.json').read_bytes()),decisions=decisions,inherited_decisions=inherited['decisions'],packet_reviews=packets,other_merged_frontier_deltas=[],reviewed_delta_paths=sorted({x['delta'] for x in specs}),research_head=BASE)
    return inherited


def source_associations(s,functions):
    p='evidence/native-front3b-20261028/NDI_BATCH_SOURCE_ASSOCIATION.json';a=s.obj(p)
    raw=s.blob(FROZEN+':'+a['source'])
    assert sha(raw)==a['source_sha256']
    fragment=b''.join(raw.splitlines(keepends=True)[a['step_line_start']-1:a['step_line_end']])
    # The lane hashes the inner loop body stripped at its outer whitespace,
    # not the complete for statement printed by the line range.
    body=fragment[fragment.index(b'{')+1:fragment.rindex(b'}')].strip()
    assert sha(body)==a['step_source_sha256']
    helper=s.read('evidence/native-front3b-20261028/NDI_K067/sources/NDI_src/crates/aspis-r1-cost-probe/src/NDI_candidate.rs')
    def block(text,start):
        begin=text.index(b'{',start);depth=1;i=begin+1
        while depth:
            if text[i]==123:depth+=1
            elif text[i]==125:depth-=1
            i+=1
        return text[begin+1:i-1].strip()
    assert block(helper,helper.index(b'fn key_iteration('))==body
    z=s.obj('evidence/native-front4b-20261028/NDM_ZERO_ERASURE.json')
    assert z['frozen_revision']==FROZEN and z['byte_identical_after_erasure']
    assert z['frozen_function_sha256']==z['erased_function_sha256']


def review_new_packets(s,audit):
    records=[
      ('native-front2-20261028','NDE','18 local conditional domains; all enclosing domains/physical/installed association retained. Packed evaluator superseded by NDN; selected binary consumer remains OPEN.'),
      ('native-front1b-20261028','NDL','Three local domains: same selected canonical decoder window, actual raw guard, canonical same-input double log. Packing final native-to-reference join and sparse tensor frame remain OPEN; prior Boolean-cut guard label corrected.'),
      ('native-front2b-20261028','NDN','Packed evaluator local canonical domain only. All other 13 remain OPEN. Nine product observations do not identify the same prefix. E015 request reference uses 0/1 versus frozen 1/2 and is invalid; compiler failures are not semantic controls.'),
      ('native-front3b-20261028','NDI','Five local domains: row, static state, query getter, static transcript initialization, batch_keys one-step induction. Full reader backing/sampler/parser/shape callers remain OPEN.'),
      ('native-front5-20261028','NDH','Ten local conditional domains only. Static digest bytes/reply does not prove SHA. Canonical decode8 excludes arbitrary-word counterexample. Registry SDK instances, QueryScan and native quotient callers remain OPEN.'),
      ('native-front4b-20261028','NDM','One bounded require_zero local bridge, terminal/reject/continuation controls and model same-caller length. Native snapshot/Vec/SDK carrier, constructors, reconstruction and scan remain OPEN.'),
      ('native-l188-20261028','NDJ','Separate root audits and release manifest; original combined import fails. Later NDR supersedes common-environment/installed-world obstruction in its exact shared aggregation scope, not whole native closure.'),
      ('native-axaudit-20261028','NDP','Strict imported-axiom enumeration/classification complete for two separately pinned forests: 3 standard,144 unreachable variants,0 root-reachable nonstandard. 32 shared axiom names have unequal types. Does not audit final NDR shared forest; import-wide shared-cohort F-AXIOM boundary remains OPEN.'),
      ('native-reconcile-20261028','NDO','23 substantive phase/observer body differences and76 historical provenance gaps retained. Installed identity is data, not native refinement. Failed unchanged phase theorem excluded; NDR repairs retained-carrier and release None use explicitly.'),
      ('native-reconcile2-20261028','NDR','Shared aggregation of headline and joint witness passes; sourceOnHeadline preserves exact quantifiers and retained tree/runtime premises on headline SDK. 3113 standalone modules pass; five verbatim thin bodies pass only in aggregation. Historical76 provenance-gap objects excluded. No arbitrary non-None adaptive transport, source/native/ELF closure or strict standalone packaging claim.'),
      ('native-chainassoc-20261028','NDQ','Observed immutable deployed devnet verifier hash fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78 mismatches current release. Pool matches. Runtime validator executable/catalog/budget attestation and L188 obligation5 remain OPEN; NDC omission cannot transfer to the historical verifier.'),
      ('devnet-plan-20261029','NDS','Existing Pool-bound registry frozen; fresh Pool-state route chosen by lead/owner current design log. No deployment or successful release execution occurred. Funding and retained-key location unresolved; no current-verifier association credit.'),
    ]
    result=[]
    for packet,pre,disposition in records:
        directory='evidence/'+packet+'/'
        ev=sorted(p for p in s.tree if p.startswith(directory) and '/' not in p[len(directory):] and (p.endswith('.md') or any(x in Path(p).name for x in ['FINAL_RESULT','VERIFICATION','PROVENANCE','STATEMENT_AUDIT','AXIOMS.json','VALIDATION.json','CHAIN_ASSOCIATION','SOURCE_PINS','AGGREGATION_PACKAGING','FINAL_OUTPUT_PINS','BUILD_RECEIPTS','STATE.json'])) and s.tree[p][1]<2*1024*1024)
        assert ev
        for p in ev:s.read(p)
        result.append(dict(prefix=pre,packet=packet,disposition=disposition,evidence=ev,native_status_promotion=pre in ['NDE','NDL','NDN','NDI','NDH','NDM']))
    # Exact shared-cohort theorem and runtime premises, not only report titles.
    p='evidence/native-reconcile2-20261028/'
    r=s.obj(p+'NDR_A001/receipt.json');src=s.read('lean/NDR_CombinedAudit.lean')
    name='AspisR1.NDR_CombinedAudit.sourceOnHeadline'
    assert r['exit_status']==0 and any("'"+name+"'" in l for l in r['print_axioms'])
    assert not any('sorryAx' in str(l) for l in r['print_axioms'])
    for line in r['print_axioms']:
        if 'axioms:' in line:assert set(x.strip() for x in line.split('axioms:',1)[1].strip().strip('[]').replace('\n','').split(',')) <= {'propext','Classical.choice','Quot.sound',''}
    matches=[(k,h) for k,h in r['source_hashes'].items() if k.endswith('NDR_CombinedAudit.lean')];assert len(matches)==1
    assert matches[0][1]==sha(src)
    assert s.obj(p+'NDR_FINAL_OUTPUT_PINS.json')['NDR_CombinedAudit.lean']['sha256']==sha(src)
    s.read(p+'NDR_A001/stdout.log');s.read(p+'NDR_L003/receipt.json');s.read(p+'NDR_L004/receipt.json')
    return result


def finish_refresh(d):
    legacy.finish_refresh(d)
    old=json.loads((HERE.parent/'native-ledger2-20261028/NDK_LEDGER.json').read_text());before={r['row']:r for r in old['rows']}
    d['refresh']['changed_rows']=[dict(row=r['row'],function=r['function'],before=before[r['row']]['bridge_status'],after=r['bridge_status'],admitted_claims=[c for c in r['selected_claims'] if c.startswith('NDT::local::')]) for r in d['rows'] if before[r['row']]['bridge_status']!=r['bridge_status']]
    d['budget']={'lean_used':0,'lean_limit':0,'kani_used':0,'kani_limit':0}


def validate_refresh(d):
    assert d['baseline_revision']==BASE
    assert d['refresh']['research_head']==BASE
    assert d['refresh']['associations_sha256']==sha((HERE/'NDT_ASSOCIATIONS.json').read_bytes())
    # Reuse ALL NDK graph/status/domain/quarantine invariants, retaining the
    # exact historical revision/recipe gates in their original validator.
    historical=copy.copy(d);historical['baseline_revision']='898a8b0da7703af67b676b18b575236940830283';historical['refresh']=dict(d['refresh'],associations_sha256=sha((legacy.HERE/'NDK_ASSOCIATIONS.json').read_bytes()))
    legacy.validate_refresh(historical)
    specs={x['id']:x for x in json.loads((HERE/'NDT_ASSOCIATIONS.json').read_text())}
    got={c['claim_id']:c for c in d['claims'] if c['claim_id'].startswith('NDT::local::')}
    assert set(got)=={k for k,v in specs.items() if v['admit']}
    for cid,c in got.items():
        spec=specs[cid];assert c['function']==spec['function']
        assert c['delta_row']==c['source_claim_text']
        assert c['named_hypotheses'][0]['statement']==spec['domain']
        assert all(h['discharged_by'] is None for h in c['named_hypotheses'])
        assert c['rule14_dependency_audit']==spec['rule14_dependency_audit'] and c['rule14_dependency_audit']
        assert [t['name'] for t in c['theorem_associations']]==spec['theorems']
        for t in c['theorem_associations']:
            assert t['source_sha256']==d['evidence_manifest'][t['source']]['sha256']
            assert t['receipt'] in c['active_support_receipts']
            for dep in t['local_import_sources']:
                assert dep['sha256']==d['evidence_manifest'][dep['source']]['sha256']
                assert dep['receipt'] in d['evidence_manifest'] and dep['source_snapshot'] in d['evidence_manifest']
        checks=c['native_feature_checks'];assert [(f['attempt'],f['positive']) for f in checks]==[(f['attempt'],f['positive']) for f in spec['native']]
        for f in checks:
            assert set(f['statement_optimized_features'])==legacy.OPTIMIZED
            assert f['all_crates_recorded']>=400 or (f['all_crates_recorded']==6 and f['feature_record_kind']=='complete isolated deployed metadata')
            assert f['scope']==spec['feature_scope']
            assert f['receipt'] in c['active_support_receipts']
            assert all(x['recovered'] for x in f['source_snapshots'] if x['source'].endswith(('.rs','.lean')))
    assert {p['prefix'] for p in d['refresh']['packet_reviews']} >= {'NDE','NDL','NDN','NDI','NDH','NDM','NDR','NCV','NCX','NDB','KNF','KNG','NCN','NCJ','NCK','NCM','NCT','NCU','NDA','NDP','NDQ','NDS'}


def summary(d,original):
    rf=d['refresh'];lines=['# NDT authoritative native composition ledger','',f"Pinned research head `{BASE}`; frozen Rust `{FROZEN}`. **Deployed 100-bit PER-ATTEMPT target not yet established.**",'',
      'Each status is LOCAL and CONDITIONAL. No native caller-domain, SDK/allocator, physical interpretation or source-to-ELF premise is discharged by this audit. The P6/D188 transport remains trust reclassification. Original NCZ/NDK snapshots and historical quarantined receipts are retained.','',
      '| Inventory | Conditional before/after | OPEN before/after | Quarantined before/after |','|---|---:|---:|---:|']
    for tx in ['TX1','TX2','all_rows','unique_functions']:
        a=rf['previous_coverage'][tx]['local_bridge_status'];b=d['coverage'][tx]['local_bridge_status'];lines.append(f"| {tx} | {a.get('CLOSED-CONDITIONAL',0)}/{b.get('CLOSED-CONDITIONAL',0)} | {a.get('OPEN',0)}/{b.get('OPEN',0)} | {a.get('quarantined',0)}/{b.get('quarantined',0)} |")
    lines+=['',f"Changed occurrences: **{len(rf['changed_rows'])}**. All 587 composed rows remain OPEN, unconditional CLOSED 0, trust-only body credit 0.",'',f"Recomputed terminal-OPEN-SCC reachability cover: **{rf['previous_frontier_size']} → {len(d['critical_path']['frontier'])}** representatives. This is an advisory conservative graph statistic, neither runtime measurement nor a sufficient proof set.",'','## Admitted and rejected deltas','', '| Function | Decision | Exact domain / reason and remaining obligations |','|---|---|---|']
    for x in rf['decisions']:lines.append('| `'+x['function']+'` | '+x['decision']+' | '+(x['domain']+'; '+x['reason']).replace('|','\\|').replace('\n',' ')+' |')
    lines+=['','## Other merged results and retained boundaries','']
    for p in rf['packet_reviews']:lines.append('- **'+p['prefix']+'**: '+p['disposition']+' Evidence: '+', '.join('`'+x+'`' for x in p['evidence'] if x.endswith('HANDOFF.md'))+'.')
    lines+=['','## Reproduction and limitations','', '`python3 evidence/native-ledger3-20261029/NDT_validate.py` independently reconstructs the pinned inventories, frozen body spans, evidence SHA256 pins, selected native verdicts/features/source archives, exact successful theorem sources/axiom audits, coverage and frontier. `--write` is explicit regeneration. `NDT_tests.py` exercises inherited NCZ/NDK invariants and new evidence mutations. The original NCZ CLI is rerun and its expected corpus-drift refusal is retained; the extended engine supplies the current snapshot.', '', 'Resolved feature metadata may be a complete isolated six-crate deployed-library graph (NDE/NDN) or an all-workspace listing. Over-unified workspace features do not supply isolated deployed parity. Archives are decoded and source hashes checked in memory; no code from archived inputs executes. Native snapshots with unrecovered ancillary controller/config inputs are explicitly labeled; no .rs/.lean body is accepted without recovery. Each selected theorem is tied to the exact successful archived source. The validator checks indexed assertions; manual theorem/contract/carrier review remains a trust boundary.', '', 'NDR shared aggregation is credited only for its exact theorem, retaining the three tree realizations and FixturePdaRuntime. Five modules lack standalone builds. NDP strict enumeration concerns separate older forests; shared-cohort import-wide F-AXIOM review is still required. NDQ records a current-release/deployed-verifier hash mismatch; no deployment association is invented. No Lean, Kani, Rust, SBF, RPC, host or wallet operation ran in this job. All compiler/solver evidence and axiom audits were reused.', '', '## Critical frontier','',original.split('## Critical path\n',1)[1].split('## Reproduction and boundaries',1)[0]]
    lines+=['','## Historical rule14 quarantine','',
      'These original harness receipts remain quarantined even where KNF/KNG static replacements restore separate local credit. Mark and the release observer retain four quarantined inventory occurrences. No global lift is inferred.','',
      '| Harness | Quarantined historical receipt |','|---|---|']
    for q in d['quarantine']:lines.append('| `'+q['harness']+'` | `'+q['receipt']+'` |')
    return '\n'.join(lines).rstrip()+'\n'
