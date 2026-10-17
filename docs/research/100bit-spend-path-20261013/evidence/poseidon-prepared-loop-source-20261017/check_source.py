from pathlib import Path
import argparse,re,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--repo',required=True,type=Path);ap.add_argument('--manifest',required=True,type=Path);ap.add_argument('--write',action='store_true');a=ap.parse_args();p=a.repo/'docs/research/100bit-spend-path-20261013';rawdir=p/'evidence/terminal-indexed-source-candidate-20261016';raw=(rawdir/'Funs.lean').read_text();types=(rawdir/'Types.lean').read_text();cut=(p/'lean/PoseidonPreparedSum3Source.lean').read_text()
names=['field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call','field.qm31_from_karatsuba_channel_sums','field.qm31_sum_products3_prepared_loop0_loop0_loop0','field.qm31_sum_products3_prepared_loop0_loop0','field.qm31_sum_products3_prepared_loop0','field.qm31_sum_products3_prepared']
def block(text,name):
 m=re.search(r'\bdef\s+'+re.escape(name)+r'(?=\s|\()',text);assert m,name
 end=text.find('\n/--',m.end());end=len(text) if end<0 else end
 s=text[m.start():end];s=re.sub(r'\nend AspisR1PoseidonPreparedSum3Source\s*\Z','',s)
 return s.strip()
records=[]
for n in names:
 r=block(raw,n);c=block(cut,n);assert re.sub(r'\s+',' ',r)==re.sub(r'\s+',' ',c),n
 records.append({'declaration':n,'raw_block_sha256':hashlib.sha256(r.encode()).hexdigest(),'cut_block_sha256':hashlib.sha256(c.encode()).hexdigest(),'comparison':'Exact declaration/body tokens; whitespace normalized only.'})
closure='def field.qm31_from_karatsuba_channel_sums.closure := Unit';assert closure in types and closure in cut
m={'raw_funs_sha256':hashlib.sha256(raw.encode()).hexdigest(),'raw_types_sha256':hashlib.sha256(types.encode()).hexdigest(),'source_sha256':hashlib.sha256(cut.encode()).hexdigest(),'declarations':records,'closure':closure,'scope':'Source cut imports existing shared field and prepared owners. The six declaration bodies match sealed indexed candidate tokens. This check does not establish whole current Rust extraction/runtime preservation or packed family equivalence.'};text=json.dumps(m,indent=2)+'\n'
if a.write:a.manifest.write_text(text)
else:assert a.manifest.read_text()==text
print('Six exact source declarations and closure matched')
