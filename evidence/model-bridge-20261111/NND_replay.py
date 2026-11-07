"""Replay unchanged reused sources privately; preserve their original owner modules."""
from NND_formal import *
import argparse
p=argparse.ArgumentParser();p.add_argument('start',type=int);p.add_argument('family',choices=['rsl','tx2']);a=p.parse_args()
if a.family=='rsl':
 names=['RSL_Base','RSL_Pool','RSL_TX2_217','RSL_TX2_234','RSL_TX2_233','RSL_TX2_242','RSL_TX2_241']
 srcdir=E.parent/'rowspec-lead-20261107'
else:
 names=['NMS_EmittedGetter','NMS_EmittedValidate','NMS_EmittedLinks','NMS_Emitted241','NMS_241EmittedLink','NMX_Emitted','NMX_EmittedLinks'];srcdir=E/'NND_reuse'
for idx,n in enumerate(names,a.start):
 src='NND_replay/'+n+'.lean';cmd=[json.loads((E/'NND_ENV.json').read_text())['env']['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NND_replay','-o','NND_objects/'+n+'.olean',src]
 r=run(f'NND_L{idx:03}','support',n,cmd,extra={src:(srcdir/(n+'.lean')).read_text()})
 if r['exit_status']:raise SystemExit(r['exit_status'])
