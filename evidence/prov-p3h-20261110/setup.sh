set -e
S=../prov-p2j-20261110
python3 - <<'P'
s=open('../prov-p2j-20261110/PCUJ_run.py').read().replace('PCUJ','PCVH').replace('codex-pc-prov-p2j-20261110','codex-pc-prov-p3h-20261110')
open('PCVH_run.py','w').write(s)
h=open('../prov-p2j-20261110/PCUJ_run_host.py').read().replace('PCUJ','PCVH')
open('PCVH_run_host.py','w').write(h)
P
grep -n "p2j\|PCUJ" PCVH_run.py PCVH_run_host.py | head
