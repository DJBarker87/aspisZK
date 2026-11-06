from pathlib import Path
import json,difflib,hashlib
E=Path(__file__).resolve().parent;p=E/'NJL_control.rs.txt';old=p.read_text();new=old.replace('reply:QM31,calls:usize}','reply:QM31,calls:usize,kind:u8}').replace('log.right=b;log.calls+=1;log.reply','log.right=b;log.kind=1;log.calls+=1;log.reply').replace('reply:NJL_q(reply),calls:0}','reply:NJL_q(reply),calls:0,kind:0}').replace('assert_eq!(log.calls,1);assert_eq!(NJL_words(log.left)','assert_eq!(log.calls,1);assert_eq!(log.kind,1);assert_eq!(NJL_words(log.left)');assert new!=old;p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_ADD_KIND.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins));p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'calls:usize,kind:u8}' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_ADD_KIND.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_ADD_KIND.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k,base in [(15,13),(16,14)]:
 x=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module='NJL_endpoint_write_cut',command=['python3','NJL_gate.py',a+'.json'],expected_time='Strengthen own native window to explicitly observe operation kind1, matching typed cut verbatim. Same arbitrary single write, no full saved prestate')
 x['native_command']=[v.replace('NJL_endpoint_lookup_cut','NJL_endpoint_write_cut')for v in x['native_command']];x['sources'].append('NJL_ADD_KIND.patch');x['collect']=[v.replace(f'NJL_K{base:03}',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
p=E/'NJL_CLOSED.json';x=json.loads(p.read_text());r=next(r for r in x['functions']if 'TX1:214'in r['rows']);r['native_pairs'][0]=['NJL_K015','NJL_K016'];r['kind_observation']='pending strengthened pair; K012/011 did not explicitly log kind, excluded as typed-cut authority until strengthened';p.write_text(json.dumps(x,indent=2)+'\n')
with (E/'NJL_FAILING_STEP.md').open('a')as f:f.write('''# Exact cut preflight correction

Review before the first combined gate found that EndpointCell.Cut includes operation kind1, while K012/K011 logged calls/operands/frame but no explicit kind field. Function identity alone was insufficient under (ai)(5). No ledger credit was claimed. Added a LOCAL kind field, wrote1 inside the same add oracle, and asserted kind1; K015/K016 is the strengthened same-name pair. Old results remain scalar frame support only. No timeout/cap increase or changed-verdict renaming. Lean statements/validation unchanged or stricter.
''')
