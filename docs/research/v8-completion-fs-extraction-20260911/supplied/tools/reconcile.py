#!/usr/bin/env python3
"""Read-only local repair discovery. No fetch, checkout, stash, reset or file edit."""
from __future__ import annotations
import argparse,hashlib,json,re,subprocess
from pathlib import Path

PIN='30a303a344dbb42e24ad8f42a8804819747942bc'
PATTERN=re.compile(r'(?:same.?body|one.?wire|audit.repair|source.refin|wire.construct)',re.I)

def git(repo:Path,*args:str,required:bool=True)->str:
    proc=subprocess.run(['git','-C',str(repo),*args],text=True,capture_output=True)
    if required and proc.returncode:raise RuntimeError(proc.stderr.strip())
    return proc.stdout.strip()

def probe(repo:Path)->dict:
    head=git(repo,'rev-parse','HEAD');status=git(repo,'status','--porcelain=v1')
    known=subprocess.run(['git','-C',str(repo),'cat-file','-e',PIN+'^{commit}'],capture_output=True).returncode==0
    ancestry=known and subprocess.run(['git','-C',str(repo),'merge-base','--is-ancestor',PIN,head],capture_output=True).returncode==0
    diff=git(repo,'diff','--name-only',PIN,head) if ancestry else ''
    candidates=[]
    for name in diff.splitlines():
        path=repo/name
        if path.is_symlink() or not path.resolve().is_relative_to(repo.resolve()):
            continue
        if path.suffix=='.lean' and path.is_file() and path.stat().st_size<2_000_000:
            text=path.read_text(errors='replace')
            if PATTERN.search(name+'\n'+text):
                candidates.append({'path':name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                    'declarations':re.findall(r'(?m)^\s*(?:theorem|lemma|def|structure)\s+(\S+)',text)})
    return {'status':'NEEDS_HUMAN_ENDPOINT_REVIEW','repo':str(repo.resolve()),'head':head,
       'branch':git(repo,'branch','--show-current'),'audited_pin':PIN,
       'descends_from_audited_pin':ancestry,'clean':not status,'dirty_paths':status.splitlines(),
       'changed_paths_since_audit':diff.splitlines(),'candidate_repair_files':candidates,
       'warning':'A matching filename or declaration name does not prove the repair complete.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    try:r=probe(a.repo)
    except (RuntimeError,OSError) as e:r={'status':'BLOCKED','reason':str(e)}
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2));raise SystemExit(1 if r['status']=='BLOCKED' else 0)
