#!/usr/bin/env python3
"""Retain reference bodies, matching the SDK impl's early-bound lifetime.
Models is a namespace only: no value is constructed, no account/guard carrier
is replaced. Actual AccountInfo inputs and std guard outputs remain unchanged.
"""
from pathlib import Path
def associated(source:str)->str:
 a=source.index('pub fn length(')
 prefix,functions=source[:a],source[a:]
 functions=functions.replace("pub fn length(account:&AccountInfo<'_>)","pub fn length(account:&AccountInfo<'a>)")
 functions=functions.replace("pub fn shared<'b,'a>(","pub fn shared<'b>(").replace("pub fn exclusive<'b,'a>(","pub fn exclusive<'b>(")
 return prefix+"pub struct Models<'a>(std::marker::PhantomData<&'a ()>);\nimpl<'a> Models<'a>{\n"+functions+'\n}\n'
if __name__=='__main__':
 import sys
 Path(sys.argv[2]).write_text(associated(Path(sys.argv[1]).read_text()))
