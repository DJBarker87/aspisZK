#!/usr/bin/env python3
"""Hash retained LLBC and exact lowering inputs; never copy binary artifacts."""
from pathlib import Path
import hashlib,json,shutil
H=Path('/home/dombarker/project-offloads/codex-cx-stage2b-20261020')
for attempt in ['parts-01','view-02','view-03','loop-04','loop-05','fields-06','owned-root-07','fresh-view-08','fresh-loop-09','reader-10','layouts-11','weights-12','cursor-13','validate-14','owned-view-root-15','owned-fresh-16','late-view-17','batch-queries-18','batch-roots-19','batch-keys-20','batch-sort-21','batch-owned-22','geometry-prefix-23','point-layout-24','weights-new-25','query-trace-26','query-pending-27','validate-index-28','batch-leaf-29','batch-tree-30','batch-three-31','prefix-index-32','accumulate-batched-33','owned-query-34','query-state-35','leaf-compare-36','index-compare-37','key-read-38','accumulate-reads-39','sort-reads-40','node-index-41','merkle-hash-42','residue-row-43','query-inline-44','resume-alpha-45','weights-iter-46','reader-queries-47','batch-borrow-48','row-borrow-49','accumulate-inline-50','query-borrow-51','residue-loops-52','residue-reads-53','trim-adapters-54','checkpoint-k-inline-55']:
 d=H/('extraction-'+attempt);out=H/'continuation-pins'/attempt;out.mkdir(parents=True,exist_ok=True)
 for p in d.glob('*-input.json'):shutil.copy2(p,out/p.name)
 p=d/'Stage2.llbc'
 if p.exists():
  raw=p.read_bytes();obj=json.loads(raw)
  (out/'llbc.json').write_text(json.dumps(dict(path=str(p),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),has_errors=obj['has_errors']),indent=2)+'\n')
