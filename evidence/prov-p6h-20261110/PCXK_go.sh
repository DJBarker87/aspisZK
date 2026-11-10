#!/bin/bash
# usage: bash PCXK_go.sh N   (runs plan scope N serially)
cd "$(dirname "$0")"
A=$(python3 -c "import json,sys;s=json.load(open('PCXK_PLAN.json'))['scopes'][int(sys.argv[1])-1];print(s['attempt'],','.join(s['modules']))" "$1")
set -- $A
python3 -I -B PCXK_run.py "$1" "$2" > "$1.client.log" 2>&1
echo "exit $?" >> "$1.client.log"
