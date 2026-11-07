#!/usr/bin/python3
"""Own package-specific deployed SDK cfg selection; no shared tool changes."""
import os,sys,json
args=sys.argv[2:]
if '--crate-name' in args and args[args.index('--crate-name')+1]=='solana_pubkey':
 args+=['--cfg','target_os="solana"','-Aexplicit_builtin_cfgs_in_flags']
with open('/home/dombarker/project-offloads/codex-pc-helpers2-20261110/PCG_rustc_commands.jsonl','a') as f:f.write(json.dumps([sys.argv[1],*args])+'\n')
os.execv(sys.argv[1],[sys.argv[1],*args])
