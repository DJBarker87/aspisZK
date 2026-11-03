from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEQ_prepare_unwrap.py'),'32','positive'],check=True)
p=E/'NEQ_native_contracts.patch';s=p.read_text();head,rest=s.split('--- /dev/null\n+++ b/crates/aspis-statement/src/NEQ_unwrap.rs\n',1);body=''.join(l[1:]+'\n' for l in rest.splitlines()[1:] if l.startswith('+'));a=body.index('fn unwrap_payload()');body=body[:a]+'''fn unwrap_payload(){let input:[u8;32]=kani::any();let other:[u8;32]=kani::any();let actual=unwrap_fixed_slice(Ok(&input));assert!(core::ptr::eq(actual,EXPECTED),"same borrowed fixed32 Ok place and lifetime");}
'''.replace('EXPECTED','&other' if mode=='negative' else '&input')
p.write_text(head+'--- /dev/null\n+++ b/crates/aspis-statement/src/NEQ_unwrap.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines()))
(E/'NEQ_UNWRAP_BORROW_CURRENT.json').write_text(json.dumps(dict(mode=mode,width=32,domain='same actual immutable array32 reference; typed Ok conversion',classification='borrowed Copy carrier for actual digest decode callers; exact pointer/lifetime, no owned-copy replacement'),indent=1)+'\n')
