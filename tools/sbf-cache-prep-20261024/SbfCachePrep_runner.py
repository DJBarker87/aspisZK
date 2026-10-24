#!/usr/bin/env python3
"""Review future command only. No process launch API."""
import argparse,json,pathlib,sys
p=argparse.ArgumentParser();p.add_argument('mode',choices=['default','devnet','pool']);p.add_argument('--run',action='store_true');a=p.parse_args()
plan=json.loads((pathlib.Path(__file__).resolve().parents[2]/'evidence/sbf-cache-prep-20261024/future-plan.json').read_text());b=next(x for x in plan['builds'] if x['mode']==a.mode)
print(json.dumps(dict(status=b['status'],cwd=b['cwd'],environment=b['environment'],unset_environment=b['unset_environment'],scope_command=b['scope_command'],expected_sha256=b['expected_sha256'],blockers=plan['execution_blockers']),indent=2))
if a.run:print('DENIED: no build authorization or execution capability.',file=sys.stderr);sys.exit(2)
