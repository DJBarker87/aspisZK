import importlib.util,json,pathlib,resource,time
p=pathlib.Path(__file__).with_name('SbfResolve_guard.py');s=importlib.util.spec_from_file_location('guard',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
t=time.monotonic();n=0;r='/exact/rustc'
for q in m.queries():assert m.permitted([r]+q,r);n+=1
for a in [[],['/proxy','-vV'],[r,'--version'],[r,'@args'],[r,'source.rs'],[r,'--emit=metadata'],[r,'--print=sysroot','source.rs']]:assert not m.permitted(a,r);n+=1
for q in m.queries():
 for extra in [['--emit=link'],['-o','x'],['--out-dir','x'],['@x'],['source.rs'],['-C','opt-level=3'],['-Zunstable-options'],['--cfg','x']]:assert not m.permitted([r]+q+extra,r);n+=1
u=resource.getrusage(0);o=dict(checks=n,exit=0,wall_seconds=time.monotonic()-t,peak_rss_bytes=u.ru_maxrss if __import__('sys').platform=='darwin' else u.ru_maxrss*1024,swap=u.ru_nswap,print_axioms='N/A',compiler_executions=0)
print(json.dumps(o));pathlib.Path('evidence/sbf-resolve-20261025/SbfResolve-tests.json').write_text(json.dumps(o,indent=2)+'\n')
