from pathlib import Path
import hashlib,re,json,subprocess,struct
E=Path(__file__).resolve().parent
r=subprocess.check_output(['git','show','4bb3b3f5:crates/aspis-r1-cost-probe/src/fast_domain.rs'],text=True)
p=Path('docs/research/100bit-spend-path-20261013/evidence/r17-query-values-wholebody-source-v1/sources/GeneratedFuns-v1.lean');s=p.read_text();out={}
for name in ['TABLE_A','TABLE_B']:
 a=r.split('const '+name,1)[1].split('];',1)[0]
 b=s.split('def fast_domain.'+name,1)[1].split(']',1)[0]
 aa=[tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+)\)',a)]
 bb=[tuple(map(int,x)) for x in re.findall(r'\((\d+)#u32,\s*(\d+)#u32\)',b)]
 assert len(aa)==len(bb)==512,(name,len(aa),len(bb));assert aa==bb
 payload=b''.join(struct.pack('<II',*x) for x in aa)
 out[name]=dict(entries=512,canonical=all(0<=x<2147483647 for pair in aa for x in pair),ordered_le32_sha256=hashlib.sha256(payload).hexdigest(),all_values_equal=True)
 assert out[name]['canonical']
(E/'NBS_TABLE_PINS.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',model_source=str(p),model_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),tables=out),indent=2)+'\n')
