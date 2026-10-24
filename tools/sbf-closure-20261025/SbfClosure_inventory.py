"""Immutable Git static input inventory. No Cargo/host/cache/network access."""
import json, pathlib, posixpath, re, tomllib
from SbfClosure_receipt import E, git, run, sha, write
REV = '8373ebf51b'
SRC = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
STAGE = '/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024'
OLD = '/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023'
PRIVATE = STAGE + '/SbfInputs-20261024-v3'
inputs = {}

def read(path, rev=REV):
    b = git('show', rev + ':' + path)
    inputs[rev+':'+path] = {'bytes':len(b), 'sha256':sha(b),
        'assessment':'REUSED immutable evidence at original source; no new live identity gate' if rev==REV else 'NEW static frozen-source inspection; no execution'}
    return b

def main():
    # Read all merged preparation scripts/reports, including retained failed sources.
    names = git('ls-tree','-r','--name-only',REV,'tools/sbf-inputs-20261024','evidence/sbf-inputs-20261024').decode().splitlines()
    for name in names:
        read(name)
    for name in ('REPORT.md','PREPARATION.md','future-plan.json','metadata-pins.json','archive-members.json','materialized-files.json','audit.json'):
        read('evidence/sbf-recapture-prep-20261024/'+name)
    for name in ('REPORT.md','current-content.json','current-global.json','current-drivers.json','complete-source-comparison.json'):
        read('evidence/sbf-identity-20261024/'+name)
    for name in ('REPORT.md','registry-join.json','registry-focused-join.json','cargo-source-research.json'):
        read('evidence/sbf-cache-prep-20261024/'+name)
    plan=json.loads(read('evidence/sbf-inputs-20261024/future-plan.json'))
    material=json.loads(read('evidence/sbf-recapture-prep-20261024/materialized-files.json'))
    archive=json.loads(read('evidence/sbf-recapture-prep-20261024/archive-members.json'))
    registry=[json.loads(x) for x in read('evidence/sbf-inputs-20261024/registry-files.jsonl').splitlines()]
    finish=json.loads(read('evidence/sbf-inputs-20261024/finish.stdout.json'))
    rows=[]
    for x in material:
        rows.append(dict(logical=OLD+'/'+x['path'], physical=STAGE+'/'+x['path'],
            type='regular',mode=x['mode'],bytes=x['bytes'],sha256=x['sha256'],set='frozen-source',association='REUSED; private copy still requires own seal'))
    for x in registry:
        rows.append(dict(logical='/home/dombarker/.cargo/'+x['path'].removeprefix('cargo/'),
            physical=PRIVATE+'/'+x['path'],type=x['type'],mode=int(x['mode'],8),
            **{k:x[k] for k in ('bytes','sha256') if k in x},set='private-registry',association='REUSED exact archive-derived private set'))
    seen=set()
    for x in finish['index_rows']:
        if x['path'] in seen: continue
        seen.add(x['path'])
        rows.append(dict(logical='/home/dombarker/.cargo/'+x['path'].removeprefix('cargo/'), physical=PRIVATE+'/'+x['path'],type='regular',mode=None,bytes=x['bytes'],sha256=x['sha256'],set='private-index',association='REUSED content; mode not recorded, blocks execution seal'))
    for x in archive:
        row=dict(logical='/home/dombarker/.cache/solana/v1.52/platform-tools/'+x['path'],
            physical=None, archive_member=x['path'],type={'0':'regular','5':'directory','2':'symlink'}[x['archive_type']],mode=int(x['archive_mode'],8),set='official-platform',association='REUSED equality only; no new private extraction/copy association')
        if row['type']=='regular':row.update(bytes=x['archive_size'],sha256=x['archive_sha256'])
        if row['type']=='symlink':row['link']=x['archive_link']
        rows.append(row)
    # Small deterministic shards; no oversized derived JSON is persisted.
    shards=[]
    for i in range(0,len(rows),1000):
        name='public-input-candidates-%02d.json' % (i//1000)
        shards.append(dict(path=name,**write(name,rows[i:i+1000])))
    allow=write('public-input-candidates.json',dict(status='FINITE PARTIAL ALLOWLIST; NOT EXECUTION-SEALED',shards=shards,forbidden_broad_binds=['/','/home','/usr','/etc','/run','/home/dombarker/.cargo','/home/dombarker/.rustup','/home/dombarker/.local'],missing=['native/runtime and outer stable package exact sets','SDK exact public subset','index modes/config metadata','private tool extraction association','pre/GO/post identity and immutable sealing']))
    root=tomllib.loads(read('Cargo.toml',SRC).decode())
    lock=tomllib.loads(read('Cargo.lock',SRC).decode())
    prepared=json.loads(read('evidence/sbf-inputs-20261024/packages.json'))
    have={(p['crate'],p['lock_checksum']) for p in prepared}
    locked=[p for p in lock['package'] if 'checksum' in p]
    missing=[dict(name=p['name'],version=p['version'],checksum=p['checksum'],source=p['source'],necessity='whole-lock upper bound; selected resolver necessity NOT established') for p in locked if (p['name']+'-'+p['version'],p['checksum']) not in have]
    manifests={};pending=['Cargo.toml']+[m+'/Cargo.toml' for m in root['workspace']['members']]
    # All workspace members and recursively named path dependencies, even optional,
    # because workspace lock resolution is wider than selected build compilation.
    while pending:
        p=pending.pop()
        if p in manifests:continue
        obj=tomllib.loads(read(p,SRC).decode());manifests[p]=obj
        def visit(x):
            if isinstance(x,dict):
                for key,value in x.items():
                    if key in ('dependencies','dev-dependencies','build-dependencies') and isinstance(value,dict):
                        for spec in value.values():
                            if isinstance(spec,dict) and isinstance(spec.get('path'),str):
                                q=posixpath.normpath(posixpath.join(posixpath.dirname(p),spec['path'],'Cargo.toml'))
                                if q.startswith('../') or q.startswith('/'):raise ValueError('external path dependency '+q)
                                if q not in manifests:pending.append(q)
                    else:visit(value)
            elif isinstance(x,list):
                for value in x:visit(value)
        visit(obj)
    tree=git('ls-tree','-r','--name-only',SRC,'crates','programs','audit/poseidon-pair-probe/program','xtask').decode().splitlines()
    scripts=[];directives=[]
    for p in tree:
        if p.endswith('/build.rs'):
            text=read(p,SRC).decode();scripts.append(dict(path=p,sha256=sha(text.encode()),text=text))
        elif p.endswith('.rs'):
            b=read(p,SRC);s=b.decode()
            selected=[dict(line=i+1,text=line.strip()) for i,line in enumerate(s.splitlines()) if re.search(r'include!|include_str!|include_bytes!|env!|option_env!|std::process|Command::|rerun-if|std::fs|File::|read_to_string',line)]
            if selected:directives.append(dict(path=p,matches=selected,assessment='lexical inventory, not proof of executed dependency closure'))
    inventory=dict(source_revision=SRC,workspace=root['workspace'],manifest_documents=manifests,
        lock_packages=len(lock['package']),locked_registry_packages=len(locked),prepared=len(prepared),
        absent_from_prepared=missing,build_scripts=scripts,source_input_operations=directives,
        source_config=read('.cargo/config.toml',SRC).decode(),
        conclusion='No Cargo ran. Historical123 is insufficient as a whole-workspace metadata proof. Missing list is exact locked upper bound, NOT a request to copy every archive; resolve separately offline after setup review. No public cache read while coordination live.')
    inv=write('static-inputs.json',inventory)
    for b in plan['builds']:
        b['environment_before']=b['environment'].copy()
        b['environment']['CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL']='3'
        b['exact_clean_inner_command']=['/usr/bin/env','-i',*[k+'='+v for k,v in sorted(b['environment'].items())],*b['command']]
        b['status']='REVIEW PROPOSAL ONLY; NO EXECUTION AUTHORITY'
    plan.update(schema='SbfClosure-future-v1',optimization_review='EXPLICIT proposed build override opt3: host build scripts/proc-macros/dependencies. Actual aspis-core/build.rs is heavy (626480 inverses plus point powers). Official Cargo1.89 precedence confirmation pending; no opt0 heavy comparison. New host fingerprints required; before/after env retained. Target argv/features/wrapper and all3 ELF pins unchanged. circle_tables byte identity and ALL3 fixed ELF gates mandatory; mismatch STOP.',status='BLOCKED: partial finite input set, no literal runtime pins, no privileged feasibility probe, no offline resolver/trace execution',claim='Input/execution preparation only; no native/Std/P7/extraction/effect/security closure')
    pp=write('future-plan.json',plan)
    write('immutable-review.json',dict(files=inputs,scope='All merged SbfInputs files read; prior archive/cache/source identity reports and manifests assessed, no live other-worker access',failures_retained=['v1 root cgroup.events absent','v2 POSIX archive type mode rejected','audit v1 absolute/relative path mismatch','unshare uid_map EPERM; no retry'],limitations='Reading/hashing immutable evidence is reuse, not revalidation of its external source.'))
    return dict(allowlist=allow,static_inputs=inv,future_plan=pp,counts=dict(source=len(material),platform=len(archive),registry=len(registry),index=len(seen),missing_locked_upper_bound=len(missing),manifests=len(manifests)),dependencies=inputs)

if __name__=='__main__':
    raise SystemExit(run('inventory.receipt.json',main))
