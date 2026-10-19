import os,sys,json
# usage: run.py env.json objects root out src [extra lean args...]
env=json.loads(open(sys.argv[1]).read())
for k,v in env.items():
    if v is None: os.environ.pop(k,None)
    else: os.environ[k]=v
objects,root,out,src=sys.argv[2:6]
os.environ["LEAN_PATH"]=objects+":"+os.environ["LEAN_PATH"]
lean=env["LEAN"]
os.execv(lean,[lean,"-j1","-M"+sys.argv[6],"-DElab.async=false","-R",root,"-o",out,src]+sys.argv[7:])
