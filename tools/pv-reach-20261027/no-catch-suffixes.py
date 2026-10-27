from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-reach-20261027/resume3';rows=json.loads((E.parent/'resume2/suffix-manifest.json').read_text());manifest=[]
for i,row in enumerate(rows):
 s=(L/f'PV_RE_DictSuffix{i:03}.lean').read_text();a=s.index('set_option autoImplicit false');b=s.index('\npv_dict_congr');s=s[a:b];s=s.replace(f'PV_RE_DictSuffix{i:03}',f'PV_RE_NoCatchSuffix{i:03}')
 chunk=i//2 if i<48 else i-24
 mod=f'PV_RE_NoCatchChunk{chunk:03}'
 text=s+f'\npv_no_catch_binds ProverRwFull.{row["source_function"]}\npv_no_catch_binds R1Z.PV_RE_NoCatchSuffix{i:03}.continueAfter\n'
 manifest.append(dict(index=i,chunk=chunk,module='R1Z/'+mod,source_function=row['source_function'],suffix=f'R1Z.PV_RE_NoCatchSuffix{i:03}.continueAfter',source_body_sha256=hashlib.sha256(s.encode()).hexdigest(),text=text))
for chunk in range(50):
 text='import R1Z.PV_RE_NoCatchGenerator\n'+ '\n'.join(r['text'] for r in manifest if r['chunk']==chunk)
 p=L/f'PV_RE_NoCatchChunk{chunk:03}.lean'
 if '--check' in sys.argv:assert p.read_text()==text
 else:p.write_text(text)
for r in manifest:r.pop('text')
p=E/'no-catch-suffix-manifest.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==manifest
else:p.write_text(json.dumps(manifest,indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(manifest),'suffixes in 50 new proof targets; old congruence checks unchanged')
