"""Pure source/package audit; no compiler, native backend, or subprocess."""
import ast
import hashlib
import json
import pathlib
import resource
import sys
import time

BASE=pathlib.Path(__file__).resolve().parents[2]
SRC=BASE/'tools/sbf-linux-20261025'
OUT=BASE/'evidence/sbf-linux-20261025'


def pin(path):
    raw=path.read_bytes()
    return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))


def main():
    start=time.monotonic()
    assert len(sys.argv)==2 and len(sys.argv[1])==40
    revision=sys.argv[1]
    sources={str(p.relative_to(BASE)):pin(p) for p in sorted(SRC.glob('*.py'))}
    assert pin(SRC/'SbfLinux_capture.py')['sha256']=='5b4f0f65abd1f3e7548a1c93bb8a8b027dd2b7346588f6f06b203cd2a2e19664'
    functions={}; imports={}
    for path in sorted(SRC.glob('*.py')):
        tree=ast.parse(path.read_text())
        functions[path.name]=[n.name for n in ast.walk(tree) if isinstance(n,(ast.FunctionDef,ast.ClassDef))]
        imports[path.name]=[ast.unparse(n) for n in ast.walk(tree) if isinstance(n,(ast.Import,ast.ImportFrom))]
        if path.name=='SbfLinux_backend.py':
            for name in ('privileged_entrypoint','fresh_host_admission'):
                fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name==name)
                assert len(fn.body)==1 and isinstance(fn.body[0],ast.Raise)
            for name in ('RUNTIME_APPROVAL','PRODUCER_ASSEMBLY'):
                a=next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in n.targets))
                assert isinstance(a.value,ast.Constant) and a.value.value is None
        if path.name=='SbfLinux_entry.py':
            assert len(tree.body)==2 and isinstance(tree.body[-1],ast.Raise)
    refs=json.loads((OUT/'SbfLinux-references.json').read_text())
    for r in refs:
        assert pin(BASE/r['path'])=={k:r[k] for k in ('sha256','size')}
        assert r['url'].startswith(('https://kernel.googlesource.com/','https://docs.python.org/'))
    package=dict(version='SbfLinux-source-only-v1',source_revision=revision,files=sources,
                 capture_source_revision='9f48e742a9df7e628e54aaed4cafead19c4e2537',
                 capture_source_path='tools/sbf-seal-20261025/SbfSeal_setup.py',
                 runtime_approval=None,runtime_files=None,producer_continuation=None,
                 privileged_entrypoint='always disabled; no flag or manifest edit enables CLI',
                 fixed_uid=1000,fixed_gid=1000,reference_manifest=pin(OUT/'SbfLinux-references.json'))
    command=dict(status='SYNTHETIC FUTURE COMMAND ONLY; entry always exits disabled',
                 argv=['/usr/bin/python3','-I','-S','-B',
                       '/var/lib/SbfLinux-20261025-v1/package/SbfLinux_entry.py'],
                 env={'PATH':'/usr/bin','LC_ALL':'C','HOME':'/probe','TMPDIR':'/tmp'},
                 entry=sources['tools/sbf-linux-20261025/SbfLinux_entry.py'],
                 future_scope=dict(MemoryHigh=3*2**30,MemoryMax=4*2**30,MemorySwapMax=0,TasksMax=64),
                 authority='NONE; fresh prospective/inside-Q0/count-once/current producer assembly missing',
                 actual_runtime_or_probe_executions=0)
    for name,data in [('SbfLinux-package.json',package),('SbfLinux-future-command.json',command)]:
        dest=OUT/name
        assert not dest.exists(), 'retain existing evidence'
        dest.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    usage=resource.getrusage(resource.RUSAGE_SELF)
    data=dict(command=['PYTHONDONTWRITEBYTECODE=1',sys.executable,
                      'tools/sbf-linux-20261025/SbfLinux_audit.py',revision],
              source_revision=revision,exit=0,wall_seconds=time.monotonic()-start,
              peak_rss_bytes=usage.ru_maxrss,swap=usage.ru_nswap,axioms='N/A',
              source_overlay=sources,functions=functions,imports=imports,
              reference_count=len(refs),package=pin(OUT/'SbfLinux-package.json'),
              command_manifest=pin(OUT/'SbfLinux-future-command.json'),
              claim='byte-identical capture copy, AST entry denials, source/reference/package hashes only')
    (OUT/'SbfLinux-source-audit.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:data[k] for k in ('exit','wall_seconds','peak_rss_bytes','swap','reference_count','axioms')}))

if __name__=='__main__':
    main()
