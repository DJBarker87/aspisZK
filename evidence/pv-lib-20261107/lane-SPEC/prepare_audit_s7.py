"""Only replace module/root arrays in inherited strict private-import driver."""
from pathlib import Path
import re,json,hashlib
L=Path(__file__).resolve().parent
R=L.parents[2]
base=(R/'lean/PV_LIB_SPEC_RawAuditSession6.lean').read_text()
start=base.index('    (#[`');end=base.index('\n  let env ←',start)
partitions={'w3':['PV_LIB_SPEC_FrozenABI','PV_LIB_SPEC_ArcImageGap'],'lanea':['PV_LIB_SPEC_LaneAStoreInput']}
report={'partitions':{},'count':0,'collector_suffix_sha256':hashlib.sha256(base[end:].encode()).hexdigest()}
for cohort,modules in partitions.items():
 roots=[]
 for m in modules:
  roots += [m+'.'+n for n in re.findall(r'^#print axioms (\w+)$',(R/'lean'/(m+'.lean')).read_text(),re.M)]
 arrays='    (#[`' + ', `'.join(modules)+'],\n     #[`'+', `'.join(roots)+'])'
 text=base[:start]+arrays+base[end:]
 dest='PV_LIB_SPEC_RawAuditSession7'+cohort.upper()
 (R/'lean'/(dest+'.lean')).write_text(text)
 report['partitions'][cohort]={'modules':modules,'roots':roots,'driver':dest,'source_sha256':hashlib.sha256(text.encode()).hexdigest()};report['count']+=len(roots)
(L/'SESSION7_RAW_ROOTS.json').write_text(json.dumps(report,indent=2)+'\n')
print('new roots',report['count'])
