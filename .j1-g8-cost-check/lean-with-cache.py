import os,sys
env=dict(os.environ)
env["LEAN_PATH"]=sys.argv[1]+":"+env.get("LEAN_PATH","")
os.execvpe("lean",["lean"]+sys.argv[2:],env)
