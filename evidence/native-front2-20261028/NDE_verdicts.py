"""Strict lane-owned verdict classification; exit 1 alone never grants credit."""
from pathlib import Path
import re,json

def classify(log):
 if 'timed out' in log or 'TIMEOUT' in log:return 'TIMEOUT'
 if 'error: could not compile' in log or 'compilation errors' in log:return 'COMPILER_FAILURE'
 if 'unwinding assertion' in log:return 'UNWIND_FAILURE'
 m=re.findall(r'\*\* (\d+) of (\d+) failed([^\n]*)',log)
 if 'VERIFICATION:- SUCCESSFUL' in log and m and m[-1][0]=='0':return 'PASS'
 if 'VERIFICATION:- FAILED' in log and m and 'undetermined' not in m[-1][2]:return 'CHECK_FAILURE'
 return 'UNRESOLVED_FAILURE'

def pair(e,positive,negative):
 for n,expected in [(positive,'PASS'),(negative,'CHECK_FAILURE')]:
  a=f'NDE_K{n:03}';log=(e/a/'stdout.log').read_text();r=json.loads((e/a/'receipt.json').read_text())
  assert classify(log)==expected,(a,classify(log),expected)
  counts=re.findall(r'\*\* (\d+) of \d+ failed',log)
  assert counts[-1]==('0' if expected=='PASS' else '1'),(a,counts)
  assert r['exit_status']==(0 if expected=='PASS' else 1),(a,r['exit_status'])
