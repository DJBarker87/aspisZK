#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';P=B/'evidence/s126-current-caller-20261021/sdk-current-incremental-20261024';p=S/'S126SdkTransportAuditV1.lean';raw=p.read_text()
a=raw.index('    for n in [');b=raw.index(' do\n',a)
t=raw[:a]+'    for n in ["AspisR1.AdapterRw.Accepted.first_call", "AspisR1.AdapterRw.Accepted.first_proof_shapes"]'+raw[b:]
t=t.replace('AspisS126SdkTransportAudit','AspisS126SdkIncrementalAudit')
(S/'S126SdkIncrementalAuditV1.lean').write_text(t)
(P/'audit-generator.json').write_text(json.dumps(dict(source=str(p.relative_to(R)),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),output_sha256=hashlib.sha256(t.encode()).hexdigest(),changes=['Change owning namespace','Compare the two AdapterRwAccepted replayed theorem types instead of four EntryPrivileges types; retain exact strict comparator and all raw closure/duplicate/unsafe checks'],scope='Read-only raw declaration comparison; no logical insertion or kernel trust'),indent=2)+'\n')
