#!/usr/bin/env python3
"""Pin current cone declaration spans; use the frozen inventory's source-cut parser."""
from pathlib import Path
import hashlib,importlib.util,json,subprocess
R=Path(__file__).resolve().parents[5]; B=R/'docs/research/100bit-spend-path-20261013'
spec=importlib.util.spec_from_file_location('inventory',B/'tools/stage2-extraction-kit/inventory.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
rows=[]
items=m.ITEMS+[(n,'crates/aspis-r1-cost-probe/src/verifier.rs',anchor,False,'function') for n,anchor in [('verifier::finish_relation_round','fn finish_relation_round('),('verifier::finish_query_dot','fn finish_query_dot(')]]
for name,p,anchor,shared,kind in items:
 raw=(R/p).read_bytes();body,start,end,line,last=m.cut.find_item(m.Blob(raw),anchor)
 rows.append(dict(name=name,path=p,kind=kind,start_byte=start,end_byte_exclusive=end,start_line=line,end_line_exclusive=last,sha256=hashlib.sha256(body).hexdigest(),file_sha256=hashlib.sha256(raw).hexdigest(),shared_with_stage1=shared))
obj=dict(source_revision=subprocess.check_output(['git','-C',str(R),'rev-parse','HEAD'],text=True).strip(),classification='VERIFIER SOURCE CHANGE',root='crate::verifier::candidate::tx2_authenticated',declarations=rows,opaque_frontiers=['aspis_core','aspis_statement','crate::weights','crate::fast_domain','crate::fast_dots','crate::fast_pairing','crate::trace'],excluded='adapter::stage2 account/SDK wrapper is inventoried but not the extraction root; external allocator/arithmetic/hash frontiers remain obligations')
p=B/'evidence/stage2-refactor-extraction-20261020/pins/extraction-inputs.json';p.write_text(json.dumps(obj,indent=2)+'\n');print(len(rows),'declaration pins')
