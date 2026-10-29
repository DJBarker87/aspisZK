"""Schema/source pins only; explicitly not native control-flow refinement."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-own-20261028'
p=R/'crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs';b=p.read_bytes();s=b.decode()
body=s.split('pub enum PoolV1PairCopyRowLinkKindV1 {',1)[1].split('\n}\n',1)[0]
body=re.sub(r'//[^\n]*','',body)
fields=re.findall(r'^    (\w+)(?:\s*\{([^}]+)\})?,',body,re.M)
expected=[('SpongeCarry',['from','to']),('OwnerOutput',[]),('NullifierKey',[]),('InputSaltHead',[]),('InputSaltTail',[]),('PrivatePathCurrent',['level']),('PrivatePathLeft',['level']),('PrivatePathRight',['level']),('ValueSource',['value']),('ConservationInput',[]),('ConservationRecipient',[]),('ConservationChange',[]),('ConservationPartial',[]),('InputSecondCommitment',[]),('InputSelectedSide',[]),('OutputSecondCommitment',[]),('OutputPairFirst',[]),('OutputPairFirstWithdrawal',[]),('OutputPairSecond',[]),('AppendCurrentLeft',['level']),('AppendCurrentRight',['level'])]
actual=[(name,re.findall(r'(\w+)\s*:\s*u8',part)) for name,part in fields]
assert actual==expected,(actual,expected)
lean=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_OWN_Link.lean';ls=lean.read_text()
for name,args in expected:
 name=name[0].lower()+name[1:]
 assert re.search(r'\| '+name+r'\b',ls)
 if args:assert '('+' '.join('«from»' if x=='from' else x for x in args)+' : UInt8)' in ls
struct=s.split('pub struct PoolV1PairCopyRowLinkV1 {',1)[1].split('\n}',1)[0]
assert re.findall(r'pub (\w+): (\w+)',struct)==[('kind','PoolV1PairCopyRowLinkKindV1'),('producer_row','u16'),('consumer_row','u16')]
records=[]
for rel in ['crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs','crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs','crates/aspis-r1-cost-probe/src/constraints.rs']:
 p=R/rel
 if p.exists():records.append(dict(path=rel,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+rel],text=True).strip()))
j=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),schema=expected,source=records,lean_schema_sha256=hashlib.sha256(lean.read_bytes()).hexdigest(),classification='source schema check, not structural K-1 substitute or native memory/ABI refinement',compiler_cohort='not invoked; any compiler/Aeneas/Charon correspondence is reclassification within existing tool trust',row_restored=False)
(E/'link-source-schema.json').write_text(json.dumps(j,indent=2)+'\n');print('21 full Link variants checked; no native binding credit')
