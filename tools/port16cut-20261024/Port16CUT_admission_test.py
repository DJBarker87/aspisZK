import importlib.util,json,pathlib,tempfile
spec=importlib.util.spec_from_file_location('gate',pathlib.Path(__file__).with_name('Port16CUT_admission.py'))
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
with tempfile.TemporaryDirectory() as t:
 root=pathlib.Path(t)
 def node(rel,pop,cap='max',procs=''):
  p=root/rel;p.mkdir(parents=True,exist_ok=True)
  for name,value in {'cgroup.type':'domain','cgroup.events':f'populated {pop}\nfrozen 0\n','memory.max':cap,
   'cgroup.controllers':'memory','cgroup.subtree_control':'memory','memory.high':'max','memory.swap.max':'0','memory.current':'0','cgroup.procs':procs}.items():
   (p/name).write_text(value)
  return p
 node('',1);node('system.slice',1);node('system.slice/docker.service',1,str(4*1024**3),'1\n')
 node('user.slice',1);node('user.slice/parent.scope',1,str(8*1024**3))
 node('user.slice/parent.scope/child',1,str(2*1024**3),'2\n')
 node('empty.scope',0,str(20*1024**3));node('background.service',1,'max','3\n')
 result=gate.snapshot(root)
 assert result['reserved_bytes']==12*1024**3,result
 rows={r['path']:r for r in result['all_cgroups']}
 assert rows['user.slice/parent.scope']['direct_process_count']==0
 assert rows['user.slice/parent.scope/child']['covering_capped_ancestor']=='user.slice/parent.scope'
 assert 'reservation_bytes' not in rows['empty.scope']
 assert 'background.service' in result['uncapped_populated']
 node('disabled',1)
 (root/'cgroup.subtree_control').write_text('memory')
 # A controller-disabled child is valid only when its parent does not delegate memory.
 node('disabled/child',1)
 (root/'disabled/cgroup.subtree_control').write_text('')
 (root/'disabled/child/cgroup.controllers').write_text('')
 (root/'disabled/child/memory.max').unlink()
 assert gate.snapshot(root)['admitted']
 (root/'system.slice/docker.service/memory.max').unlink()
 try:gate.snapshot(root)
 except FileNotFoundError:pass
 else:raise AssertionError('unreadable required data did not fail closed')
 print(json.dumps({'nested_dedup':True,'empty':True,'direct_zero_child_live':True,
  'system_docker_visible':True,'uncapped_visible':True,'missing_data_fails_closed':True}))
