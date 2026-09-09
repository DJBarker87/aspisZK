#!/usr/bin/env python3
"""Call the existing authorized Pushover helper without importing its monitor."""
import ast,json,pathlib,sys,urllib.request,urllib.parse
p=pathlib.Path('/Users/dominic/ZK/private/aspis-config/v5-mainnet-20260724/monitor_v5_mainnet.py')
t=ast.parse(p.read_text());nodes=[n for n in t.body if isinstance(n,ast.FunctionDef) and n.name in ['load_env','pushover_once'] or isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id in ['PUSHOVER_ENV','PUSHOVER_API'] for x in n.targets)]
ns={'Path':pathlib.Path,'json':json,'urllib':urllib,'log':lambda *a:None}
exec(compile(ast.Module(body=nodes,type_ignores=[]),str(p),'exec'),ns)
ns['pushover_once'](sys.argv[1],sys.argv[2]);print('Milestone helper invoked; no credentials printed.')
