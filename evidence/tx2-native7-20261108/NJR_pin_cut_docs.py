from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
source=(E/'NJR_parent.rs.txt').read_text();sha=hashlib.sha256(source.encode()).hexdigest()
def lines(name):
 start=source.index('fn '+name+'(');end=source.index('\n}',start)+2
 return '\n'.join(line.strip() for line in source[start:end].splitlines() if 'assert' in line)
items=[('NJR_Cuts.lean','pending','pending_destination',lines('pending_destination')),('NJR_Cuts.lean','queryReturn','query_weights/query_raw/query_scalars',lines('query_check<const C:usize>')),('NJR_Cuts.lean','flushStep','flush_receiver_window + flush_destination_window',lines('flush_receiver_window')+'\n'+lines('flush_destination_window')),('NJR_ReaderCut.lean','Cut','reader_backing','assert_eq!(r.at,self.at);\n'+lines('reader_backing'))]
for file,name,harness,quote in items:
 p=E/file;s=p.read_text();start=s.index('def '+name+' ');end=s.rfind('-/',0,start)
 assert end>=0
 previous=s.rfind('\nNative source:',0,end)
 if previous>s.rfind('/--',0,start):
  s=s[:previous]+s[end:];end=previous
 note=f'\nNative source: NJR_parent.rs.txt, sha256 {sha}, harness {harness}.\nAssertion transcription: `{quote}`\nNative ownership/capacity facts stay in the certificate packet; no additional\nmodel field, child success or endpoint equation is inferred here.\n'
 s=s[:end]+note+s[end:];p.write_text(s)
(E/'NJR_CUT_SOURCE_PIN.json').write_text(json.dumps(dict(source='NJR_parent.rs.txt',sha256=sha,definitions=[dict(module=f,definition=n,harness=h,assertion_quote=q) for f,n,h,q in items]),indent=2)+'\n')
