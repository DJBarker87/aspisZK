"""Collect safe metadata only after the already submitted differential completes."""
from pathlib import Path
import json,subprocess,re,hashlib,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-uc5-20261103';H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-uc-20261029'
# Read-only, no process submission, no witness/proof/recovery/private input copies.
done=subprocess.check_output(['ssh',H,'cat '+D+'/native91110/done-status.txt'],text=True).strip();assert done=='0',done
O=E/'differential';O.mkdir(exist_ok=True)
names=subprocess.check_output(['ssh',H,'ls '+D+'/final-gates/uc5/differential-final/'],text=True).splitlines()
selected=[n for n in names if re.fullmatch(r'(comparison-\d+|secret-scan-\d+|summary|secret-scan-summary)\.json',n)]
assert len(selected)==202,len(selected)
code="from pathlib import Path; import json; p=Path("+repr(D+'/final-gates/uc5/differential-final')+"); names="+repr(selected)+"; print(json.dumps({n:(p/n).read_text() for n in names}))"
payload=json.loads(subprocess.check_output(['ssh',H,'python3 -c '+shlex.quote(code)],text=True))
assert set(payload)==set(selected)
for name,raw in payload.items():(O/name).write_text(raw)
summary=json.loads((O/'summary.json').read_text());assert summary['passed'] and summary['pairs']==100 and summary['fully_executed_prover_calls']==200
scans=[json.loads((O/f'secret-scan-{i}.json').read_text()) for i in range(100)]
hits=[dict(pair=i,**h) for i,s in enumerate(scans) for h in s['hits']]
# asset is intentionally public: plan.prove sets payment.asset_id to this word,
# and the frozen public statement encoder emits it. Retain all matches, do not
# claim literal disjointness of raw records and public outputs.
private_hits=[h for h in hits if h['field']!='asset']
result=dict(evidence_class='finite exact-byte search over complete raw secret fields and full record; not noninterference',pairs=100,files=sum(len(s['scanned']) for s in scans),protected_fields=['input_key','input_salt','input_value','change_key','change_salt','recipient_owner','recipient_salt','recipient_value','record'],protected_secret_field_gate_pass=not private_hits,key_salt_record_gate_pass=all(s['key_salt_record_gate_pass'] for s in scans),raw_all_fields_disjoint=not hits,private_hits=private_hits,public_asset_hits=[h for h in hits if h['field']=='asset'],custody_records_checked_in_memory=100,exclusions=['raw output pipe is caller-owned custody endpoint','unchanged baseline fixture legacy private files are not final-client outputs'],limitations=['Full-width raw needles only, not an individual-byte-disjointness claim or a proof against arbitrary encodings/side channels.','Every raw asset match is retained. The asset identifier is a public statement field; no claim that all212 input bytes are individually absent from public bytes.','The progress.json elapsed field was shadowed by a field-offset loop variable; it is not collected as wall-time evidence. Final summary elapsed uses the original global start; receipt wall is authoritative.'])
(O/'secret-gate.json').write_text(json.dumps(result,indent=2)+'\n')
# No marker modification or timing launch; record observed window state.
q=subprocess.check_output(['ssh',H,"python3 -c 'import json,time,os; p=\"/home/dombarker/project-offloads/QUIET_WINDOW.json\"; print(json.dumps(dict(now=time.time(),marker=json.load(open(p)) if os.path.exists(p) else None)))'"],text=True)
(E/'quiet-window-final-observation.json').write_text(q)
print(json.dumps(dict(differential_pass=True,pairs=100,protected_secret_field_gate_pass=not private_hits,public_asset_matches=len(hits)-len(private_hits),files=result['files'])))
