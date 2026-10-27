import subprocess,sys
compile=['/home/dombarker/.cargo/bin/rustc','-C','opt-level=3',sys.argv[1],'-o',sys.argv[2]]
subprocess.run(compile,check=True)
subprocess.run([sys.argv[2]],check=True)
