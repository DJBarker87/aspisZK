"""Additive NEM continuation: every NEL and earlier check remains active."""
from pathlib import Path
import sys,json,argparse
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(R/'evidence/slice-s-compose4-20261101'))
import NEL_validate as predecessor
read=predecessor.read

def compose(base,packet,reviewed):
 return predecessor.compose(base,packet,reviewed)

def main():
 p=argparse.ArgumentParser();p.add_argument('--write',type=Path);a=p.parse_args()
 out=compose(read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json'),read(E/'NEM_LEDGER_DELTA.json'),read(E/'NEM_REVIEWED_CERTIFICATES.json'))
 if a.write:a.write.write_text(json.dumps(out,indent=1)+'\n')
 print(json.dumps(predecessor.predecessor.summary(out),indent=1))
if __name__=='__main__':main()
