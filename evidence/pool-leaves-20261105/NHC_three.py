from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,gen,args,h,expected in [('NHC_K009','NHC_request_box.py',['error','negative'],'pair_forest::NHC_RequestBox::association',1),('NHC_K010','NHC_loader_native.py',['positive'],'pair_forest_dispatch::NHC_Loader::association',0),('NHC_K011','NHC_loader_native.py',['negative'],'pair_forest_dispatch::NHC_Loader::association',1)]:
 subprocess.run([sys.executable,str(E/gen),*args],check=True,capture_output=True)
 r=subprocess.run([sys.executable,str(E/'NHC_kani_run.py'),a,h],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,r.returncode,flush=True)
 if r.returncode!=expected:print((r.stdout+r.stderr)[-1000:]);sys.exit(r.returncode or 1)
