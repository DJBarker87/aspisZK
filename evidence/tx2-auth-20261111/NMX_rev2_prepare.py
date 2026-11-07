"""Separate canonical revision2 owners and new prefix-owned dependent modules."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
fs={p.stem:p.read_text() for p in E.glob('*.lean')};ds={m:re.findall(r'^import (\w+)',s,re.M) for m,s in fs.items()}
def closure(m,seen=None):
 seen=set() if seen is None else seen
 if m in seen:return seen
 seen.add(m)
 for d in ds.get(m,[]):closure(d,seen)
 return seen
cl=closure('NMX_SevenSourceFold')
changed={m for m in cl if m.startswith('NMX_') and any(d.startswith(('RSL_','NMS_RSL')) for d in closure(m))}
rename={m:'NMX_R2_'+m.removeprefix('NMX_') for m in changed}
rows=[]
for m in sorted(changed):
 s=fs[m]
 s=re.sub(r'\bNMX_\w+',lambda z:rename.get(z[0],z[0]),s)
 s=re.sub(r'\(RSL\.RS\.ofExcept \((RSL\.OwnedAccount\.data \([^\n]+?\))\)\)',r'(\1)',s)
 # Canonical continuation definitions have simple, unparenthesized account arguments.
 s=re.sub(r'\(RSL\.RS\.ofExcept \((RSL\.OwnedAccount\.data \w+)\)\)',r'(\1)',s)
 s=s.replace('(RSL.RS.ofExcept (RSL.verifierCheckpoint verifierCheckpoint verifier false))','(RSL.verifierCheckpoint verifierCheckpoint verifier false)')
 if m=='NMX_Heterogeneous':s=s.replace('import NMS_RSLRefine\n','')
 if m=='NMX_Semantics':
  s=s.replace('RSL.RS.ofExcept (RSL.verifierCheckpoint (NMX_R2_Carrier.account a) (NMX_R2_Carrier.key program) writable)','RSL.verifierCheckpoint (NMX_R2_Carrier.account a) (NMX_R2_Carrier.key program) writable')
  s=s.replace('match a.bytes with\n   | .Ok v => RSL.RS.pure v.deref\n   | .Err e => RSL.RS.throw (NMX_R2_Carrier.error e)','RSL.RS.ofCloned (NMX_R2_Carrier.reply (fun v => v.deref) a.bytes)')
 if m=='NMX_CommandTransport':
  s=s.replace('import NMX_R2_Semantics','import NMX_R2_Semantics\nimport NMX_R2_CloneTransport')
  start=s.index(' := by',s.index('theorem data '));end=s.index('\ntheorem pda ',start)
  s=s[:start]+''' := by
 change NMX_R2_Heterogeneous.Refines bytes
  (RSL.RS.ofCloned (reply (fun v => v.deref) a.bytes))
  (RSL.RS.ofCloned (reply (fun v => v.val.map byte) a.bytes))
 cases h : a.bytes with
 | Ok v => exact NMX_R2_HeterogeneousPrimitives.pure bytes v.deref
 | Err e => exact NMX_R2_CloneTransport.error bytes (error e)
''' + s[end:]
 (E/(rename[m]+'.lean')).write_text(s)
 rows.append(dict(original=m,original_sha256=sha(E/(m+'.lean')),revision2=rename[m],revision2_sha256=sha(E/(rename[m]+'.lean'))))
(E/'NMX_REV2_SOURCE_PROVENANCE.json').write_text(json.dumps(rows,indent=1)+'\n')
(E/'NMX_REV2_MODULES.json').write_text(json.dumps(sorted(rename.values()),indent=1)+'\n')
