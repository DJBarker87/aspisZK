#!/usr/bin/env python3
"""Pin reused extraction and compare its shipped source functions verbatim."""
import hashlib,json,subprocess,re
from pathlib import Path
E=Path(__file__).resolve().parent.parent
file='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
old='78192937489e12a7f1d8b421622d32b1ad9beab3'
current=Path(file).read_text()
previous=subprocess.check_output(['git','show',old+':'+file],text=True)
def body(text,name):
 start=re.search(r'\bfn '+name+r'(?:<[^>]*>)?\s*\(',text).start()
 left=text.index('{',start);depth=1;i=left+1
 while depth:
  depth+=(text[i]=='{')-(text[i]=='}');i+=1
 return text[start:i]
rows=[]
for name in ['public_bytes','private_public','withdrawal_public']:
 a,b=body(previous,name),body(current,name)
 assert a==b,name
 rows.append(dict(function=name,verbatim_equal=True,sha256=hashlib.sha256(b.encode()).hexdigest(),bytes=len(b.encode())))
record=dict(historical_extraction_source_revision=old,current_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_path=file,functions=rows,
 note='Public metadata is copied in carriers but omitted exactly as in public_bytes. Generated module imports are ported to Env J; computational definitions and namespaces are unchanged.')
(E/'serializer-source-pins.json').write_text(json.dumps(record,indent=2)+'\n')
