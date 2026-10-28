import json,re,pathlib,hashlib
E=pathlib.Path(__file__).parent
inv=json.load(open('evidence/native-inv2-20261027/NBI2_INVENTORY.json'))
rows={}
def add(packet,member,status,source,detail):
 key=packet+'::'+member
 row=rows.setdefault(key,dict(id=key,packet=packet,member=member,credited_status=status,sources=[],detail=[]))
 if source not in row['sources']:row['sources'].append(source)
 if detail not in row['detail']:row['detail'].append(detail)
 if 'CONDITIONAL' in status:row['credited_status']='CLOSED-CONDITIONAL'
for l in inv['closed_leaves']:
 add('P6',l['function'],'CLOSED',l['evidence'],'13 opaque leaves; checkpoint final scope superseded by KNE_FINDING.md and its DriverEstablishedDomain, source schedule and initialized-spare qualifications' if 'checkpoint' in l['function'] else 'Exact local domain in cited leaf packet; inherited fidelity qualifications retained')
for p in sorted(pathlib.Path('evidence').glob('native-*/*BRIDGE.md')):
 packet=p.name.split('_')[0]
 if not re.fullmatch(r'N[BC][A-Z]',packet):continue
 for no,line in enumerate(p.read_text().splitlines(),1):
  if not line.startswith('|'):continue
  cols=[x.strip() for x in line.strip('|').split('|')]
  if len(cols)<2:continue
  status=cols[1]
  if re.match(r'(?:\*\*)?(?:CLOSED|Reused CLOSED|inherited CLOSED)',status) and not status.startswith('OPEN'):
   member=cols[0].strip('` ');member=re.sub(r'\s+(?:F\d+|(?:lib|verifier|trace)\.rs:.*)$','',member)
   add(packet,member,'CLOSED-CONDITIONAL' if 'CONDITIONAL'in status or 'conditional'in status else 'CLOSED',str(p)+':'+str(no),' | '.join(cols[1:]))
# Full member ledgers supplement prose summaries (do not promote source-model-only rows).
for p in sorted(pathlib.Path('evidence').glob('native-*/*STATUS.json')):
 if not re.match(r'N[BC][A-Z]_',p.name):continue
 j=json.loads(p.read_text())
 if not isinstance(j,list):continue
 for r in j:
  status=r.get('native_status',r.get('status',''))
  if not status.startswith('CLOSED'):continue
  if 'id' not in r:continue
  add(p.name.split('_')[0],r['id'],status,str(p),json.dumps(r))
# U06 has unit-wide conditional status; U02 NBP explicitly closes all16 inventoried members.
p=pathlib.Path('evidence/native-tx2h-20261028/NBQ_U06_BRIDGE.md')
for line in p.read_text().splitlines():
 if not line.startswith('|') or line.startswith(('| Member','|---')):continue
 c=[x.strip() for x in line.strip('|').split('|')]
 add('NBQ',c[0],'CLOSED-CONDITIONAL',str(p),' | '.join(c[1:]))
for f in inv['functions']:
 if f['bridge_unit']=='U02':add('NBP',f['id'],'CLOSED','evidence/native-tx2g-20261028/NBP_U02_BRIDGE.md','All16 U02 members locally closed; original per-member domain and qualifications retained')
add('NBQ','powers','CLOSED-CONDITIONAL','evidence/native-tx2h-20261028/NBQ_U07_BRIDGE.md','powers29 only; canonical gamma, one-step native windows, K-1 qualification')
for packet,source in [('NBQ','evidence/native-tx2h-20261028/NBQ_U00_BRIDGE.md'),('NBS','evidence/native-tx2i-20261028/NBS_U00_BRIDGE.md')]:
 add(packet,'error','CLOSED-CONDITIONAL',source,'Returning log/frame domain only; formatting/SDK/runtime retained')
add('NCA','inactive serializer statement5','CLOSED-CONDITIONAL','evidence/native-prepare4-20261028/NCA_prepare_BRIDGE.md:19','One actual zip body and Prepared::new serializer argument; lower native bridges retained; complete prepare OPEN')
# Restored native harness families in merged mitigation/reverification bridges are narrow credits, not whole-member closures.
for r in json.load(open('evidence/kani-mitig-20261028/KMX_RERUN_STATUS.json')):
 if r['status']=='PASS':add('KMX',r['id'],'CLOSED narrow replay','evidence/kani-mitig-20261028/KMX_RERUN_STATUS.json',json.dumps(r))
for r in json.load(open('evidence/kani-reverify2-20261028/KMZ_ROW_CREDITS.json'))['rows']:
 if r['status']=='CONFIRMED':add('KMZ',r['original'],'CLOSED narrow restored property','evidence/kani-reverify2-20261028/KMZ_ROW_CREDITS.json',json.dumps(r))
# Merge abbreviated and fully qualified member names within each packet where exact unique suffix matches.
for k in list(rows):
 if k not in rows:continue
 r=rows[k]
 if '.rs::'in r['member']:continue
 candidates=[q for q in rows.values() if q['packet']==r['packet'] and '.rs::'in q['member'] and (q['member'].endswith('::'+r['member']) or q['member'].split('.rs::')[-1]==r['member'])]
 if len(candidates)==1:
  q=candidates[0];q['sources']+=r['sources'];q['detail']+=r['detail'];del rows[k]
out=sorted(rows.values(),key=lambda r:r['id'])
(E/'NCS_CREDIT_INVENTORY.json').write_text(json.dumps(dict(rows=out,count=len(out),scope='Each historical merged packet/member credit retained separately; duplicates of a member within packet merged. OPEN native/model-only and controls excluded.'),indent=2)+'\n')
print('credited packet/member families',len(out))
