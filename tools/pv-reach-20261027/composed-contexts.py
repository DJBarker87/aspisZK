from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-reach-20261027/resume4'
rows=json.loads((E.parent/'resume2/suffix-manifest.json').read_text());out=[]
for i,row in enumerate(rows):
 s=(L/f'PV_RE_DictSuffix{i:03}.lean').read_text();a=s.index('set_option autoImplicit false');b=s.index('\npv_dict_congr');s=s[a:b].replace(f'PV_RE_DictSuffix{i:03}',f'PV_RE_ComposedSuffix{i:03}')
 s='import R1Z.PV_RE_ComposedContextsGenerator\n'+s+f'\npv_composed_source_contexts ProverRwFull.{row["source_function"]}\npv_composed_source_contexts R1Z.PV_RE_ComposedSuffix{i:03}.continueAfter\n'
 p=L/f'PV_RE_ComposedChunk{i:03}.lean'
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
 out.append(dict(module='R1Z/'+p.stem,source_function=row['source_function'],suffix=f'R1Z.PV_RE_ComposedSuffix{i:03}.continueAfter',sha256=hashlib.sha256(s.encode()).hexdigest()))
p=E/'composed-manifest.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print(len(out),'new composed-context chunks; no whole-run reduction')
