#!/usr/bin/env python3
"""Pin original and factored object inputs for read-only declaration comparison."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021/s6-sdk-source-cuts-20261024';S=B/'lean-candidates/s126-caller-boundary-20261021';roots=[Path('/tmp/s126-current-caller-20261021-objects')]+[Path(x) for x in Path('/tmp/s126-s6-sdk-first-path-20261024.txt').read_text().strip().split(':')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def resolve(n):
 rel=Path(*n.split('.')).with_suffix('.olean');return next(r/rel for r in roots if (r/rel).exists())
mods=['MultiproofConeCanonical','S2LeadInterface','S2Z_Oracle','S2W_ExtractionBoundary','S2W_EntryWriteHistory','S2W_CommittedCheckpoint','S2W_ReturnedCheckpoint','S2W_AccountObservations','S2W_D189Interpretation','S2W_SnapshotJoin','S2W_D189Entry','S2W_D189Wrappers','S2W_DigestExtraction','S2W_D189Consolidation','AdapterRwLeadInputs','S2W_NativeConsolidation']
rows=[];files=[]
for n in mods+['S6SdkDependencyFactorV1','S6SdkSourceCutTypesV1']:
 p=resolve(n);rows.append(dict(module=n,path=str(p),factored=n.startswith('S6')))
 for ext in ['', '.server','.private']:
  q=Path(str(p)+ext)
  if q.exists():files.append(dict(path=str(q),bytes=q.stat().st_size,sha256=sha(q)))
text=json.dumps(rows);Path('/tmp/s126-sdk-declaration-audit-20261024.json').write_text(text+'\n')
(E/'declaration-audit-input.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',modules=rows,files=files,scope='Read-only original/factored complete ConstantInfo comparison. Not theorem construction, kernel reconstruction or release replay.'),indent=2)+'\n')
# Reuse the reviewed comparator and module reader byte for byte, under a new namespace.
p='docs/research/100bit-spend-path-20261013/lean/Port18COHERENCE_CompatibilityLoad.lean';src=subprocess.check_output(['git','show','904745b496:'+p]).decode();body=src[src.index('def sameDeclaration'):src.index('\ndef load')]
head='import Lean\nopen Lean\nnamespace AspisS6SdkDeclarationAudit\n'
main=r'''
def run : IO Unit := do
  let input ← IO.FS.readFile "/tmp/s126-sdk-declaration-audit-20261024.json"
  let j ← IO.ofExcept (Json.parse input)
  let rows ← IO.ofExcept j.getArr?
  let mut originals : Std.HashMap Name ConstantInfo := {}
  let mut factors : Array ConstantInfo := #[]
  for row in rows do
    let path ← IO.ofExcept (row.getObjValAs? String "path")
    let factored ← IO.ofExcept (row.getObjValAs? Bool "factored")
    let data ← readComplete path
    for c in data.constants do
      if factored then factors := factors.push c
      else originals := originals.insert c.name c
  let mut missing := 0
  let mut identical := 0
  let mut proofOnly := 0
  let mut different := 0
  for c in factors do
    if let some old := originals[c.name]? then
      if c.name == `AspisR1.S2W_D189Wrappers.first then
        IO.println ("FIRST_TERMS " ++ (Json.mkObj [("original",toJson (reprStr old.value?)),
          ("factored",toJson (reprStr c.value?))]).compress)
      let same := sameDeclaration old c
      let sameType := old.type == c.type
      let sameValue := old.value? (allowOpaque := true) == c.value? (allowOpaque := true)
      let proof := old.isTheorem && c.isTheorem && sameType
      IO.println ("DECL " ++ (Json.mkObj [("name",toJson c.name.toString),
        ("identical",toJson same),("same_type",toJson sameType),
        ("same_value",toJson sameValue),("proof_only",toJson proof)]).compress)
      if same then identical := identical+1
      else if proof then proofOnly := proofOnly+1
      else different := different+1
    else
      missing := missing+1
      IO.println ("MISSING " ++ c.name.toString)
  IO.println ("SUMMARY " ++ (Json.mkObj [("identical",toJson identical),
    ("proof_only",toJson proofOnly),("different",toJson different),("missing",toJson missing)]).compress)
#eval run
end AspisS6SdkDeclarationAudit
'''
out=head+body+'\n'+main;(S/'S6SdkDeclarationAuditV1.lean').write_text(out)
(E/'declaration-audit-helper.json').write_text(json.dumps(dict(revision='904745b496',path=p,source_sha256=hashlib.sha256(src.encode()).hexdigest(),copied_body_sha256=hashlib.sha256(body.encode()).hexdigest(),scope='Exact reviewed sameDeclaration/readComplete definitions. Read-only IO only; no setEnv/addDecl or theorem is produced.'),indent=2)+'\n')
print(json.dumps(dict(modules=len(rows),files=len(files))))
