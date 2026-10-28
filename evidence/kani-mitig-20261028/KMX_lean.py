from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KMX_host as h
a=sys.argv[1];assert not (E/(a+'.json')).exists()
cfg=dict(attempt=a,kind='lean',sources=['KMX_CopyMeaning.lean'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-M7000','KMX_CopyMeaning.lean','-o',h.CACHE+'/KMX_CopyMeaning.olean'],timeout=180,env={'PATH':'/home/dombarker/.elan/bin:/usr/bin:/bin'},deps_fingerprint={'imports':'Std from pinned Lean v4.32.0 sysroot; no project imports'},expected_time='small symbolic induction only')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
subprocess.run([sys.executable,str(E/'KMX_host.py'),a],check=True)
