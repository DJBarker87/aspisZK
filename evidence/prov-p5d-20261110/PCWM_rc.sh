#!/bin/bash
# usage: bash PCWM_rc.sh PCWM_Lnnn  -- exit, wall, rss, swaps, axioms set, error count
cd "$(dirname "$0")"
python3 -B - "$1" <<'P'
import json,sys,re,subprocess
a=sys.argv[1];r=json.load(open(a+'/receipt.json'))
ax=set(re.sub(r'\s+',' ',x.split('axioms:')[1].strip()) if 'axioms:' in x else 'none' for x in r['print_axioms'])
err=subprocess.run('xz -dc %s/stdout.log.xz | grep -c " error"'%a,shell=True,capture_output=True,text=True).stdout.strip()
print(a,'exit',r['exit_status'],'wall',round(r['wall_seconds'],1),'rss_kib',r['peak_rss_kib'],'swaps',r['swaps'],'n_axioms',len(r['print_axioms']),ax,'errors',err)
P
