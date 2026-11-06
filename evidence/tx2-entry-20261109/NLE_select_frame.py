from pathlib import Path
import json,lzma,sys,re
E=Path(__file__).resolve().parent;field=sys.argv[1];assert field in ['public','proof','checkpoint']
idx=json.loads((E/'NLE_INPUTS.json').read_text());h=idx['attempts']['NLE_K006']['NLE_src/crates/aspis-r1-cost-probe/src/NLE_auth_window.rs'];s=lzma.decompress((E/'NLE_INPUTS'/(h+'.xz')).read_bytes()).decode()
for other,index,value in [('proof','pi','pv'),('public','ui','uv'),('checkpoint','ci','cv')]:
 if other==field:continue
 s=re.sub(r' let '+index+r':usize=.*?;kani::assume\('+index+r'<[0-9]+\);\n','',s)
 s=s.replace('let '+value+':u8=kani::any();','')
 s=re.sub(r'\n core::ptr::addr_of_mut!\(\(\*ptr\)\.'+other+r'\).*?\.write\('+value+r'\);','',s)
index,value={'public':('ui','uv'),'proof':('pi','pv'),'checkpoint':('ci','cv')}[field]
a=s.index(' let good=');b=s.index('\n assert!(good',a);s=s[:a]+' let good=input.'+field+'['+index+']=='+value+';'+s[b:]
s=s.replace('NLE full Result independent oracle replies SAME descriptors arbitrary coordinate frame','NLE isolated '+field+' arbitrary coordinate frame')
from NLE_patch import save
save('NLE_auth_window',s,'NLE_frame_'+field)
print('NLE isolated '+field+' frame selected')
