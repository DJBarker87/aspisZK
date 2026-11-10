#!/bin/bash
# usage: bash PCQD_why.sh RUN  -- show exits and the tail of the stdout log
r=$1; cd "$(dirname "$0")"
python3 - "$r" <<'P'
import json,sys
r=sys.argv[1];p=json.load(open(f'{r}_emitted/{r}_PINS.json'))
print({k:p.get(k) for k in ('charon_exit','aeneas_exit','exit','controller_error')})
P
xz -dc $r/stdout.log.xz 2>/dev/null | grep -vE '^warning|^\s*(\||-->|=|[0-9]+ \|)|^\s*$' | tail -${2:-25} | cut -c1-300
