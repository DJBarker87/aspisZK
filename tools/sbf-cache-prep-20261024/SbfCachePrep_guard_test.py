#!/usr/bin/env python3
import dataclasses,hashlib,importlib.util,json,pathlib,resource,subprocess,sys,time
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-cache-prep-20261024';start=time.monotonic()
s=importlib.util.spec_from_file_location('SbfCachePrepGuard',T/'SbfCachePrep_guard.py');m=importlib.util.module_from_spec(s);sys.modules[s.name]=m;s.loader.exec_module(m)
checks=[]
def check(name,ok):checks.append(dict(name=name,passed=bool(ok)));assert ok,name
base=m.Event(m.COMPILER,m.COMPILER_SHA,('-vV',),'metadata',True,True)
check('uninstalled broker denies even query',not m.decide(dataclasses.replace(base,complete_interception=False))['allow'])
for args in [('-vV',),('--print','sysroot')]:
    event=dataclasses.replace(base,argv=args);out=m.decide(event);check('exact real query forwarded '+repr(args),out['allow'] and out['forward']==args)
for args in [('-vV','evil.rs'),('--print','sysroot','--emit=link','evil.rs'),('@response',),('--crate-name','serde','src/lib.rs'),('--crate-name','aspis_core','/owned/src/lib.rs')]:
    check('unsealed compiler command denied '+repr(args),not m.decide(dataclasses.replace(base,argv=args))['allow'])
for path,phase in [('/cache/build/serde/build-script-build','build-script'),('/bin/sh','build-script-child'),('/usr/bin/cc','native-child'),('/bin/echo','unknown')]:
    check('pre-exec child denied '+phase,not m.decide(m.Event(path,'unsealed',(),phase,True,True))['allow'])
check('changed compiler identity denied',not m.decide(dataclasses.replace(base,sha256='changed'))['allow'])
w=m.Event(m.WRAPPER,m.WRAPPER_SHA,(m.COMPILER,'-vV'),'metadata',True,True)
check('original wrapper forwards verbatim',m.decide(w)['forward']==w.argv)
check('wrapper child still pinned',m.decide(w)['require_child']==(m.COMPILER,m.COMPILER_SHA))
# Concrete counterexample supported by Cargo custom_build.rs: a cached build
# script is exec'd directly and never passes through RUSTC_WRAPPER.
wrapper_hook_observes=['compiler'];actual_execs=['compiler','cached-build-script']
check('wrapper-only coverage rejected',set(actual_execs)-set(wrapper_hook_observes)=={'cached-build-script'})
u=resource.getrusage(0)
r=dict(checks=checks,scope='Offline decisions only; no real interception, Cargo/compiler/build script or exec test. PRE-EXEC integration and warm compatibility NOT established.',receipt=dict(command=[sys.executable,'-B',str(pathlib.Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),print_axioms='N/A'),dependencies={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (T/'SbfCachePrep_guard.py',pathlib.Path(__file__))})
(E/'guard-tests.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(checks=len(checks),receipt=r['receipt']),indent=2))
