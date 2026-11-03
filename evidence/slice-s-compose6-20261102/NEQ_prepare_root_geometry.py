from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','negative']
subprocess.run([sys.executable,str(E/'NEQ_prepare_root_prefix.py'),'positive'],check=True)
p=E/'NEQ_native_contracts.patch';s=p.read_text();head,rest=s.split('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_root_prefix.rs\n',1);body=''.join(l[1:]+'\n' for l in rest.splitlines()[1:] if l.startswith('+'))
body+='\n#[kani::proof]\nfn root_geometry(){assert!(MASTER_OFFSET==8&&CHECKPOINT_ACCOUNT_OFFSET==40&&SELECTED_LANE_ACCOUNT_OFFSET==72&&CHECKPOINT_SEQUENCE_OFFSET==104&&HISTORICAL_ANCHOR_OFFSET==112&&LATE_STATEMENT_OFFSET==144&&POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES==1520&&PAYMENT_STATEMENT_OFFSET=='+('1665' if mode=='negative' else '1664')+'&&POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES==1880);}\n'
p.write_text(head+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEQ_root_prefix.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines()))
(E/'NEQ_ROOT_GEOMETRY_CURRENT.json').write_text(json.dumps(dict(mode=mode,classification='frozen compile-time expression geometry, no protocol loop'),indent=1)+'\n')
