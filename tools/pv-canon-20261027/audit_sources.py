from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-canon-20261027';rows=[]
for p in sorted(D.glob('PV_Canon_*.lean')):
 s=p.read_text();bad=re.findall(r'\b(?:sorry|admit|native_decide|implemented_by)\b|^\s*axiom\s',s,re.M)
 declared=re.findall(r'\btheorem\s+(\w+)',s);printed=re.findall(r'^#print axioms (\w+)',s,re.M)
 rows.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),theorems=declared,missing_axiom_prints=sorted(set(declared)-set(printed)),forbidden=bad))
(E/'source-audit.json').write_text(json.dumps(rows,indent=2)+'\n');assert not any(r['forbidden'] or r['missing_axiom_prints'] for r in rows);print(len(rows),'source modules audited')
