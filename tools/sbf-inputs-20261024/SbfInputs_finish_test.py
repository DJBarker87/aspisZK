import hashlib,importlib.util,json,pathlib,resource,subprocess,sys,time
start=time.monotonic();p=pathlib.Path(__file__).with_name('SbfInputs_finish_host.py');s=importlib.util.spec_from_file_location('finish',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
expected={'a':'1/a','ab':'2/ab','abc':'3/a/abc','serde_core':'se/rd/serde_core'}
for a,b in expected.items():assert m.index_rel(a)==b
for bad in ['../x','/tmp/a','Name','']:
 try:m.index_rel(bad)
 except AssertionError:pass
 else:raise AssertionError(bad)
cmd=m.probe_command();assert cmd[:8]==['/usr/bin/unshare','--user','--map-current-user','--mount','--net','--pid','--fork','--'];assert cmd[8:14]==['/usr/bin/python3','-I','-S','-B','-c',cmd[-1]];assert 'os.getuid()!=0' in cmd[-1]
u=resource.getrusage(0);r=dict(exit=0,tests=9,namespace_executed=False,command=[sys.executable,'-B',__file__],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),inputs={str(q):hashlib.sha256(q.read_bytes()).hexdigest() for q in [p,pathlib.Path(__file__)]},wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swap=u.ru_nswap,print_axioms='N/A')
with pathlib.Path('evidence/sbf-inputs-20261024/finish-tests.json').open('x') as f:json.dump(r,f,indent=2);f.write('\n')
print('9 index/control-flow tests passed; namespace not run')
