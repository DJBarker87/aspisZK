"""Generate one callee-cut byte window from the CLOSED NGD row schedule."""
from pathlib import Path
import json,hashlib,difflib,sys
E=Path(__file__).resolve().parent

def generate(kind,row=0):
 size=32 if row in [2,14] else 896 if 15<=row<=24 else 3712 if row==25 else 928 if row==26 else 0
 src=32+5*row if row<=2 else 64+5*row if row<=14 else 155+453*(row-15) if row<=25 else 6546
 dst=32+5*row if row<=2 else 64+5*row if row<=14 else 171+901*(row-15) if row<=25 else 12898
 stored=size if row<14 else size//2
 if kind=='row':x=dict(MODE=0,ROW=row,SRC=src,DST=dst,PAYLOAD=size,STORED=stored,INPUT_START=16+src,INPUT_WIDTH=5+stored,OUTPUT_START=dst,OUTPUT_WIDTH=5+size,LOGICAL_SUFFIX=13831-dst-5-size,TAIL_Y1=928)
 elif kind=='prefix':x=dict(MODE=1,ROW=0,SRC=0,DST=0,PAYLOAD=32,STORED=32,INPUT_START=16,INPUT_WIDTH=32,OUTPUT_START=0,OUTPUT_WIDTH=32,LOGICAL_SUFFIX=13799,TAIL_Y1=928)
 elif kind=='values':x=dict(MODE=2,ROW=0,SRC=0,DST=0,PAYLOAD=928,STORED=464,INPUT_START=7031,INPUT_WIDTH=464,OUTPUT_START=13831,OUTPUT_WIDTH=928,LOGICAL_SUFFIX=0,TAIL_Y1=0)
 else:raise ValueError(kind)
 assert x['INPUT_START']+x['INPUT_WIDTH']<=7495 and x['OUTPUT_START']+x['OUTPUT_WIDTH']+x['LOGICAL_SUFFIX']+x['TAIL_Y1']==14759
 text=(E/'NHF_stage_window.template.rs.txt').read_text()
 for k,v in x.items():text=text.replace('@'+k+'@',str(v))
 assert '@' not in text
 (E/'NHF_stages.rs.txt').write_text(text)
 pins=json.loads((E/'NHF_SOURCE_PINS.json').read_text());pins['crates/aspis-r1-cost-probe/src/NHF_stages.rs']=hashlib.sha256(text.encode()).hexdigest();(E/'NHF_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
 # Replace only this module's addition; the wide-view input/control body is unchanged.
 p=E/'NHF_native.patch';patch=p.read_text();a=patch.index('--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NHF_stages.rs\n');b=patch.index('--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NHF_wide.rs\n',a)
 patch=patch[:a]+''.join(difflib.unified_diff([],text.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NHF_stages.rs'))+patch[b:];p.write_text(patch)
 return dict(kind=kind,row=row,parameters=x,source_sha256=hashlib.sha256(text.encode()).hexdigest())
if __name__=='__main__':print(json.dumps(generate(sys.argv[1],int(sys.argv[2]) if len(sys.argv)>2 else 0)))
