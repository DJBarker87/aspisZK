#!/usr/bin/env python3
import os,sys
args=sys.argv[1:]
for i,a in enumerate(args):
 if a.startswith('--emit='):
  args[i]=a+',llvm-ir'+('' if '--crate-name' in args and args[args.index('--crate-name')+1]=='libsecp256k1' else ',mir')
args+=['-Zmir-include-spans=yes']
os.execv(args[0],args)
