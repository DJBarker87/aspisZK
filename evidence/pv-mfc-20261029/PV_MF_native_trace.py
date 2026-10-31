"""Trace exact native receipt entries; no association inferred from file names."""
from pathlib import Path
import subprocess,json,hashlib,collections
D=Path(__file__).resolve().parent
old=json.load(open(D.parent/'pv-mfb-20261029/classifications.json'))
cache={}
def file(p):
 if p not in cache:
  b=subprocess.check_output(['git','show','HEAD:'+p]);cache[p]=dict(path=p,blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip(),sha256=hashlib.sha256(b).hexdigest())
 return cache[p]
def evidence(p):file(p);return p
traces=[]
for x in old:
 if x['category']!='C' or x['input']['path'].endswith('.lean'):continue
 t=x['input'];p=t['receipt_path'];b=subprocess.check_output(['git','show','HEAD:'+p]);v=json.loads(b)
 for k in t['pointer'].strip('/').split('/'):
  v=v[int(k)] if isinstance(v,list) else v[k]
 # Preserve original pointer payload, not a guessed association by path stem.
 n=x['record'];status='C';rows=[];chain=[p+t['pointer']];why=''
 if n in [437,438]:
  rows=['V352','V354','V357','V360'];status='B';chain += [evidence('evidence/pv-l2c-20261028/resume-d371/REPORT.md'),'recount9: V352,V354,V357,V360 = OPEN']
  why='The native source checks feed L2C input/guard and field-cut diagnostics. Its final report explicitly retains all four endpoint rows OPEN and zero premise removal. Those diagnostics are not a restoring native-source binding for a credited callback row.'
 elif n==550:
  rows=['V165','V166','V167'];status='B';chain += [evidence('evidence/pv-runjoin13-20261027/REPORT.md'),'records adapter extraction: no accepted R_shipped; source/fixture/compiler-return obligations OPEN']
  why='The stale source is the proof-only owned adapter in this MIR metadata build, not a generation receipt for an accepted shipped Records law. The report rejects the successful empty records extraction and leaves stage3 open. No credited restoring theorem consumes this adapter as a shipped-source law.'
 elif 584<=n<=589:
  rows=['V165','V166','V167'];status='B';chain += [evidence('evidence/pv-srcid3-20261026/RESUME6-REPORT.md'),evidence('evidence/pv-srcid3-20261026/RESUME8-ROOT-STATUS.md'),'native root/compiler association: OPEN; source-parent cells 0/21']
  why='These exact native pins belong to srcid root/compiler/reference gates. The final source-root report retains full merkle_node_compress/native compiler association and all21 source-parent cells as obligations. Literal/model root cells do not restore that native association. No currently credited native callback closure is obtained from these old pins.'
 elif n in [497,498,499]:
  status='B';rows=['V178'] if n in [497,498] else ['V182']
  chain += [evidence('tools/pv-relink-20261028/bind-v178.py') if n in [497,498] else evidence('tools/pv-relink-20261028/bind-v182.py'),evidence('evidence/pv-rdb1-20261028/REPORT.md'),evidence('evidence/pv-rdb1-20261028/rows/'+rows[0]+'.json')]
  if n in [497,498]:why='The two archived path snapshots are read by bind-v178. V178 has a checked allocation-effect discrepancy and remains OPEN at recount9; its narrower historical contents law is not a credited whole-row restoration.'
  else:why='The archived string snapshot is read during the initial classify-structural replay. V182 restoration subsequently uses the separately pinned installed1.94.1 deployed source and the new complete append/reserve/copy binding (rows/V182.json -> v182-deployed-binding.json). The old archived file pin is superseded, not silently transferred to that restored source. Its Lean statement is unchanged, but this particular archived-source input is not the deployed restoration source.';chain += [evidence('evidence/pv-rdb1-20261028/v182-deployed-binding.json')]
 elif 'pv-batch2-' in p:
  rows=['V256','V257','V258','V259','V260','V261'];chain += [evidence('evidence/pv-batch2-20261027/batch2f/ROW-STATUS.json'),evidence('evidence/pv-batch2-20261027/batch2f/V258.md'),evidence('evidence/pv-batch2-20261027/batch2f/V259.md'),'recount9: RDB2F/RDB2C/RDCD3/B1 selected restorations']
  why='A historical batch2 packet reaches the same operation families, but the full-tree source inventories do not isolate which changed function is consumed by the later deployed restoration. The constructor/materialize records name old structural and source-input boundaries; a complete old-input/body/configuration-to-current-restoring-theorem chain has not been established. The presence of a later restoring theorem alone does not discharge this edge.'
 elif 'pv-cb3-' in p:
  rows=['V195','V219','V246','V254'];chain += [evidence('evidence/pv-cb3-20261026/RESUME6_ROWS.md'),evidence('evidence/pv-cb3-20261026/RESUME6_FINAL_REPORT.md'),'recount9: V242 OPEN; V246 replaced by RDCD statement bridge; V195/V219/V254 qualified restorations']
  why='The resume6 inventory is a broad snapshot for many support/extraction attempts. The final row table distinguishes five retained rows from failed or reference-only native gates, but does not attribute this exact changed file/pointer to a retained source body. The missing edge is the receipt-pinned body/call-cone selection for this input, including its generation/native configuration; matching a filename to a live row would be unsound.'
 elif 'pv-b3p6-' in p:
  rows=['V228','V229','V243'];chain += [evidence('evidence/pv-b3p6-20261028/STATUS.json'),'recount9: V228 Install132.reference; V229 OWNH literal; V243 Closure226.complete_result']
  why='The old aggregate lib.rs pin occurs only in its aggregate manifest under an exact-hash search of the b3p6 evidence. Later132/133/226 generation and structural packets use per-operation owned inputs. The required hash chain from this particular old aggregate lib.rs version to a credited per-operation extraction/structural binding is absent; no historical certificate migration is inferred.'
 assert why,(n,p)
 traces.append(dict(record=n,category=status,input=t,pointer_payload=v,receipt=file(p),candidate_rows=rows,chain=chain,reason=why))
(D/'native-chains.json').write_text(json.dumps(dict(records=traces,evidence_files=list(cache.values())),indent=2)+'\n')
print(collections.Counter(x['category'] for x in traces),len(traces))
