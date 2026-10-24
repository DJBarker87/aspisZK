#!/usr/bin/env python3
"""Derive incremental raw reader from previously reviewed export machinery."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';P=B/'evidence/s126-current-caller-20261021/sdk-current-incremental-20261024'
p=S/'S126SdkCurrentExportV1.lean';source=p.read_text();t=source.replace('AspisS126SdkCurrentExport','AspisS126SdkIncrementalExport')
t=t.replace('(needed done : Std.HashSet String) :','(needed done excluded : Std.HashSet String) :')
t=t.replace('work m data needed done','work m data needed done excluded')
t=t.replace('done.contains (nameString c.name))','done.contains (nameString c.name) && !excluded.contains (nameString c.name))')
t=t.replace('  let mut done : Std.HashSet String := {}\n  for (m,p)', '  let baseline ← IO.ofExcept (config.getObjValAs? (Array String) "baseline_names")\n  let excluded := baseline.foldl (fun s n => s.insert n) ({} : Std.HashSet String)\n  let mut done := excluded\n  for (m,p)')
t=t.replace('scan m p needed done','scan m p needed done excluded')
t=t.replace('("constants",toJson done.size)', '("constants",toJson (done.size-excluded.size)),("baseline_constants",toJson excluded.size)')
assert t!=source and t.count('excluded : Std.HashSet String')==2
(S/'S126SdkIncrementalExportV1.lean').write_text(t)
(P/'generator.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),source_sha256=hashlib.sha256(source.encode()).hexdigest(),output_sha256=hashlib.sha256(t.encode()).hexdigest(),changes=['initialize discovered constant set with hash-pinned immutable base names','do not serialize base names again','report incremental and baseline counts separately','retain exact reader/region-lifetime/type/value/group/recursor/serialization machinery'],scope='IO raw data only, no environment insertion or kernel trust'),indent=2)+'\n')
