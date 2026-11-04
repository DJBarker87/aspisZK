#!/usr/bin/env python3
"""Read-only compiler diagnostics for each selected local crate in one Cargo check."""
import sys,subprocess,pathlib,json,os
rustc,*args=sys.argv[1:]
name=args[args.index('--crate-name')+1] if '--crate-name' in args else ''
b=pathlib.Path(__file__).resolve().parent
if name in ['aspis_core','aspis_statement','aspis_r1_cost_probe','aspis_r1_cost_probe_program']:
 for mode,suffix,extra in [('mir','mir', ['-Zmir-opt-level=1']),('hir,typed','hir',[]),('mir','mir0',['-Zmir-opt-level=0'])]:
  cmd=[rustc,*args,*extra,'-Zunpretty='+mode]
  env=os.environ.copy();env.pop('CARGO_MAKEFLAGS',None);env.pop('MAKEFLAGS',None)
  with (b/('NFZ_'+name+'.'+suffix)).open('w') as out,(b/('NFZ_'+name+'.'+suffix+'.stderr')).open('w') as err:
   rc=subprocess.run(cmd,stdout=out,stderr=err,env=env).returncode
  with (b/'NFZ_COMPILER_COMMANDS.jsonl').open('a') as f:f.write(json.dumps(dict(crate=name,mode=mode,representation=suffix,command=cmd,exit=rc))+'\n')
  if rc:sys.exit(rc)
os.execv(rustc,[rustc,*args])
