"""Recover one original committed source input: logical-path destination-path."""
import sys
from pathlib import Path
sys.dont_write_bytecode=True
import NKB_resolve
name,destination=sys.argv[1:3];p=Path(destination);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(NKB_resolve.read(name));print('Recovered '+name+' with its SHA-256 checked')
