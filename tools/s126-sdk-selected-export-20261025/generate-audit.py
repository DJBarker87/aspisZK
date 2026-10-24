#!/usr/bin/env python3
"""Compositional raw graph audit; baseline closure is immutable and reused."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';P=B/'evidence/s126-current-caller-20261021/sdk-selected-cut-export-20261025';p=S/'S126SdkTransportAuditV1.lean';raw=p.read_text();t=raw.replace('AspisS126SdkTransportAudit','AspisS126SdkSelectedCutAudit')
t=t.replace('  let mut cs : Std.HashMap Name ConstantInfo := {}', '''  let baseline ← IO.ofExcept (config.getObjValAs? (Array String) "baseline_names")
  let baselineParts ← IO.ofExcept (config.getObjValAs? (Array (String × String)) "baseline_transport")
  let mut baseNames : Std.HashSet Name := {}
  for (_,path) in baselineParts do
    let data ← readComplete path
    for c in data.constants do baseNames := baseNames.insert c.name
  let expected := baseline.foldl (fun s n => s.insert n) ({} : Std.HashSet String)
  unless baseNames.size == expected.size && baseNames.toArray.all (fun n => expected.contains n.toString) do
    throw (IO.userError "baseline exact-name inventory mismatch")
  let mut cs : Std.HashMap Name ConstantInfo := {}''')
t=t.replace('    for c in data.constants do\n', '    for c in data.constants do\n      if baseNames.contains c.name then throw (IO.userError s!"overwrites immutable base constant: {c.name}")\n')
t=t.replace('unless cs.contains dep do unresolved', 'unless cs.contains dep || baseNames.contains dep do unresolved')
t=t.replace('("constants",toJson cs.size)', '("constants",toJson cs.size),("baseline_constants",toJson baseNames.size)')
assert t!=raw and t.count('baseNames.contains')==2
(S/'S126SdkSelectedCutAuditV1.lean').write_text(t)
(P/'audit-generator.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),output_sha256=hashlib.sha256(t.encode()).hexdigest(),changes=['Owning namespace','Read exact Name values from hash-pinned closed baseline raw parts; no printed-name parsing','Reject any new declaration at a baseline name','Permit dependencies in new fragments OR immutable closed baseline','Report baseline count separately; exact strict comparator/full opaque/inductive/recursor dependency extraction and raw-table guards unchanged'],scope='Compositional untrusted raw data graph check; not typechecking or environment insertion. Existing two base closure audits and all selected cached input identities are reused unchanged.'),indent=2)+'\n')
