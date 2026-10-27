"""Exact source-pinned handoff for the remaining native-boundary closure."""
import pathlib,json
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume9';rows=json.load(open(E/'native-project-closure.json'));old={r['module'] for r in json.load(open(E/'project-closure.json'))};good=set(old);history=[]
for p in sorted(E.glob('receipt-[0-9]*.json')):
 r=json.load(open(p))
 for m in r['modules']:
  if m['accepted']:good.add(m['module'])
  if 40210<=r['attempt']<=40296:history.append(dict(module=m['module'],attempt=r['attempt'],accepted=m['accepted']))
remaining=[r for r in rows if r['module'] not in good];mapping={r['module']:r for r in rows}
def closure(m,s=None):
 s=set() if s is None else s
 if m not in mapping or m in s:return s
 s.add(m)
 for d in mapping[m]['imports']:closure(d,s)
 return s
roots={m:sorted(closure(m)-good) for m in ['R1Z.PV_Src_NativeInput','R1Z.PV_Src_FrozenFixtures','R1Z.PV_Src_PublicDeploymentAssociation','R1Z.PV_Src_ExternalAssociation','R1Z.PV_Src_RecordAssociation']}
(E/'remaining-native-prerequisites.json').write_text(json.dumps(remaining,indent=2)+'\n')
(E/'remaining-native-prerequisites.txt').write_text('\n'.join(r['module'] for r in remaining)+'\n')
(E/'native-goal-dispositions.json').write_text(json.dumps(dict(roots=roots,remaining=len(remaining),native_history_reconstructed_from_all_numbered_receipts=history),indent=2)+'\n')
print('remaining native prerequisites',len(remaining),'first',remaining[0]['module'] if remaining else None)
for m,s in roots.items():print(m,len(s))
