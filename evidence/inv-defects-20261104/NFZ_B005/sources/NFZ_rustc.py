#!/usr/bin/env python3
"""Record exact stable compiler launches, retaining Cargo's one-slot jobserver."""
import sys,os,json,pathlib
rustc,*args=sys.argv[1:]
assert len(os.sched_getaffinity(0))==1
assert os.environ['CARGO_BUILD_JOBS']=='1'
assert '-C codegen-units=1' in os.environ['RUSTFLAGS']
assert not any(a.startswith('-Z') for a in args)
b=pathlib.Path(__file__).resolve().parent
with (b/'NFZ_COMPILER_COMMANDS.jsonl').open('a') as f:
 f.write(json.dumps(dict(command=[rustc,*args],affinity=sorted(os.sched_getaffinity(0)),CARGO_BUILD_JOBS=os.environ['CARGO_BUILD_JOBS'],RUSTFLAGS=os.environ['RUSTFLAGS'],CARGO_MAKEFLAGS=os.environ.get('CARGO_MAKEFLAGS'),MAKEFLAGS=os.environ.get('MAKEFLAGS')))+'\n')
os.execv(rustc,[rustc,*args])
