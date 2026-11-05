from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
borrowed=(E/'NHB_contains.rs.txt').read_text().split('#[kani::requires(n==7)]')[0]
owned=(E/'NHB_owned.rs.txt').read_text().removeprefix('use super::*;\n')
word=(E/'NHB_word.rs.txt').read_text().replace('NHB_invert','NHB_reply_corrupt')
for n in range(7,23):word=word.replace(f'{n} => NHB_contains_{n}(a,n,x)',f'{n} => NHB_contains_{n}(*a,n,x)')
cursor=(E/'NHB_cursor.rs.txt').read_text().removeprefix('use super::*;\n').replace('NHB_invert','NHB_reply_corrupt')
(E/'NHB_active.rs.txt').write_text(borrowed+owned+word+cursor)
rows=[]
for n in range(23):
 k=3+2*n if n<=6 else 20 if n==7 else 22+2*(n-8)
 rows.append(dict(length=n,function='NHB_contains_'+str(n),parameter='borrowed fixed22 array' if n<=6 else 'owned fixed22 array',positive=f'NHB_K{k:03}',negative=f'NHB_K{k+1:03}',domain=f'n=={n}; every array word and x arbitrary',lean_theorems=['AspisR1.NHB_Membership.reference_eq','AspisR1.NHB_Membership.prefix_membership'],native_status='PENDING_VALIDATION'))
(E/'NHB_MEMBERSHIP_CALLEES.json').write_text(json.dumps(rows,indent=2)+'\n')
p=E/'NHB_run.py';s=p.read_text();needle="if os.environ.get('NHB_INVERT'):config['env']['RUSTFLAGS']+=' --cfg NHB_invert'";s=s.replace(needle,needle+"\n if os.environ.get('NHB_BYTE_INVERT'):config['env']['RUSTFLAGS']+=' --cfg NHB_reply_corrupt'");p.write_text(s)
