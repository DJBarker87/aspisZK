from NCJ_host import *
admit('NCJ_SETUP004')
# The initial private archive omitted workspace members. Add only source/manifests
# required by frozen path dependencies; never change dependency declarations.
roots=['xtask','audit/poseidon-pair-probe/program','docs/research/v8-r0-zk-20261009/refine','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3/check','docs/research/v8-r0-zk-20261009/c3/build','.cargo']
files=subprocess.check_output(['git','ls-tree','-r','--name-only','4bb3b3f5',*roots],text=True).splitlines()
files=[p for p in files if p.endswith(('.rs','.toml','.lock'))]
blob=subprocess.check_output(['git','archive','4bb3b3f5',*files])
r=subprocess.run(['ssh',H,'tar -xf - -C '+shlex.quote(B+'/NCJ_src')],input=blob,capture_output=True);assert r.returncode==0,r.stderr
cfg=json.loads((E/'NCJ_FROZEN_GRAPH.json').read_text());cfg['attempt']='NCJ_FROZEN_GRAPH3';cfg['expected_time']='frozen metadata after adding missing unchanged path-dependency sources'
r=launch(cfg);assert r['exit_status']==0
m=json.loads(next(l for l in (E/'NCJ_FROZEN_GRAPH3/stdout.log').read_text().splitlines() if l.startswith('{')))
keys={p['id']:json.dumps([p['name'],p['version'],p.get('source')],separators=(',',':')) for p in m['packages']}
graph={'packages':sorted(keys.values()),'edges':sorted([keys[n['id']],sorted(keys[d] for d in n['dependencies'])] for n in m['resolve']['nodes'])}
(E/'NCJ_frozen_graph.json').write_text(json.dumps(graph,indent=2)+'\n')
