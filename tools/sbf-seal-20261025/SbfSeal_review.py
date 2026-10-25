"""Local immutable Git-only packet builder. No remote path is opened."""
import ast
import difflib
import hashlib
import json
from pathlib import Path
import subprocess
import SbfSeal_setup as setup

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=ROOT/'evidence/sbf-seal-20261025'
ENTRY='50ab99cfbf3febcea66046e017be3e619ca8c732'
PRODUCER='f29c3e0e8c'


def blob(rev,path):
    return subprocess.check_output(['git','show',rev+':'+path],cwd=ROOT)


def write(name,data):
    raw=(json.dumps(data,sort_keys=True,indent=2)+'\n').encode()
    assert len(raw)<5_000_000
    (OUT/name).write_bytes(raw)


def main():
    references=[]
    sources=[(ENTRY,'tools/sbf-closure-20261025/SbfClosure_setup.py'),
             (ENTRY,'tools/sbf-closure-20261025/SbfClosure_trace.py'),
             (ENTRY,'evidence/sbf-closure-20261025/FAILURES.md'),
             (ENTRY,'evidence/sbf-closure-20261025/synthetic-tests.receipt.json'),
             (ENTRY,'evidence/sbf-resolve-20261025/SbfResolve-sets.json'),
             (ENTRY,'evidence/sbf-resolve-20261025/SbfResolve-audit.json'),
             (ENTRY,'evidence/sbf-resolve-20261025/SbfResolve-REPORT.md'),
             (PRODUCER,'tools/resource-rss-go-20261025/ResourceRssGO_host.py'),
             (PRODUCER,'tools/resource-rss-go-20261025/ResourceRssGO_adapter.py'),
             (PRODUCER,'tools/resource-rss-go-20261025/ResourceRssGO_guard.py'),
             (PRODUCER,'tools/resource-rss-go-20261025/ResourceRssGO_sources.py'),
             (PRODUCER,'evidence/resource-rss-go-20261025/ResourceRssGO-REPORT.md'),
             ('f7b90c82300c8a2409625fefb5dc529db6547f9c','tools/resource-stability-20261025/ResourceStability_evaluator.py'),
             ('5756082d85e4d6784de4566059d6a9845604342a','tools/resource-stat-20261024/ResourceStat_go.py')]
    for rev,path in sources:
        raw=blob(rev,path)
        full=subprocess.check_output(['git','rev-parse',rev],cwd=ROOT,text=True).strip()
        references.append(dict(revision=full,path=path,**setup.digest(raw)))
    write('SbfSeal-reference-pins.json',references)
    old=blob(ENTRY,sources[0][1]).decode()
    new=(HERE/'SbfSeal_setup.py').read_text()
    for name,oldtext,newtext in (
        ('SbfSeal-setup-full.diff',old,new),
        ('SbfSeal-setup-AST.diff',ast.dump(ast.parse(old),indent=2),ast.dump(ast.parse(new),indent=2))):
        (OUT/name).write_text(''.join(difflib.unified_diff(oldtext.splitlines(True),newtext.splitlines(True),
                                                          fromfile='immutable-SbfClosure_setup',tofile='candidate-SbfSeal_setup')))
    sets=json.loads(blob(ENTRY,'evidence/sbf-resolve-20261025/SbfResolve-sets.json'))
    base='/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/SbfResolve-20261025-v1'
    rows=[]
    for row in sets['rows']:
        def mapping(pin):
            assert pin['path'].startswith(base+'/cargo/')
            return dict(physical=pin['path'],logical='/cargo/'+pin['path'].split('/cargo/',1)[1],
                        sha256=pin['sha256'],size=pin['bytes'])
        rows.append(dict(name=row['name'],version=row['version'],checksum=row['checksum'],
                         archive=mapping(row['archive']),index=mapping(row['index']),
                         selected_build_necessity=False))
    assert len(rows)==428 and len({(r['name'],r['version']) for r in rows})==428
    assert len({r['index']['logical'] for r in rows})==394
    write('SbfSeal-input-map.json',dict(status='NONEXECUTABLE FUTURE MAPPING; no remote read',
        packages=rows,private_manifest=sets['cache_manifest'],
        complete_per_file_mapping_available=False,
        reason='Private 19714-file manifest only hash+size available; same-uid0700 is not immutable',
        sdk_root_suffix='/solana-release/bin/platform-tools-sdk/sbf',
        criterion=dict(path='/home/dombarker/.cache/solana/v2.3.3/criterion',
                       entered=False,copied=False,policy='deny unless finite required release-manifest resolution OR separately proved unreachable and omitted'),
        native_python_closure='PARTIAL; loader/dlopen/stdlib/pyc/import allowlist needs exact finite manifest'))
    tracepath='evidence/sbf-resolve-20261025/SbfResolve-raw-query-2.trace'
    trace=blob(ENTRY,tracepath)
    specs={
        'shared-state':('CLONE_FILES','shared CLONE_FS/FILES/THREAD state unsupported'),
        'wait':('wait4(','strict subset has no wait semantics'),
        'negative-probe':('ENOENT','requires sealed absence/complete directory membership'),
        'unfinished':('<unfinished','split records unsupported'),
        'resumed':('resumed>','split records unsupported'),
        'loader-cache':('ld.so.cache','loader/cache runtime mapping partial'),
        'pyc':('.pyc','Python import/pyc closure partial')}
    fixtures={}
    lines=trace.decode().splitlines()
    for label,(needle,why) in specs.items():
        line=next(line for line in lines if needle in line)
        fixtures[label]=dict(line=line,unsupported_reason=why)
    write('SbfSeal-trace-fixtures.json',dict(source_revision=ENTRY,path=tracepath,
        trace_pin=setup.digest(trace),fixtures=fixtures,
        limitation='lexical extraction only; raw records also lack timestamps expected by strict parser; missing close/dup/fcntl capture; no parser PASS'))
    write('SbfSeal-future-command.json',dict(status='PENDING REVIEW; NO EXECUTION AUTHORITY',
          root=setup.ROOT,uid=setup.UID,gid=setup.GID,argv=list(setup.PROBE),env=setup.ENV,
          approved_manifest_sha256=[],runtime_manifest=None,
          command_note='Only execve of fixed argv after every host/kernel/runtime/FD gate; no sudo/root shell CLI'))
    package={p.name:setup.digest(p.read_bytes()) for p in sorted(HERE.glob('*.py'))}
    write('SbfSeal-package-pins.json',dict(entry=ENTRY,files=package,
          implementation_lines=sum(len((HERE/n).read_text().splitlines()) for n in
              ('SbfSeal_setup.py','SbfSeal_admission.py','SbfSeal_boundary.py')),
          privileged_execution='DISABLED unconditionally; no CLI; no approved manifests',
          elf_pins=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',
              devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',
              Pool='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548')))
    print('SbfSeal immutable reference packet generated; no host/backend operations')


if __name__=='__main__':main()
