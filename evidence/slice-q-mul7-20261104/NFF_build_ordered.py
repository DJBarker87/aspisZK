from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NFF_CORRECTED_PAYLOAD.json').read_text());key='crates/aspis-r1-cost-probe/src/NFF_dots.rs';s=p[key]
s=s.replace('calls:[u8;8] }','calls:[u8;8],order:[usize;8],next:usize }')
s=s.replace(' log.left[lane]=a;', ' log.order[log.next]=lane;log.next+=1;\n log.left[lane]=a;')
s=s.replace('calls:[0;8]};','calls:[0;8],order:[99;8],next:0};')
s=s.replace(' assert_eq!(log.calls[lane],1);',' assert_eq!(log.next,8);assert_eq!(log.order[lane],lane);\n assert_eq!(log.calls[lane],1);')
p[key]=s;(E/'NFF_ORDERED_PAYLOAD.json').write_text(json.dumps(p));(E/'NFF_dots.rs.txt').write_text(s)
