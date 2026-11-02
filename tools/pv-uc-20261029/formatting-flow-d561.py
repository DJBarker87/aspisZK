"""Check the source anchors used by the D561 formatting/data-flow review."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];base=R/'tools/r1-cost-probe/src/bin'
files=[base/'user_client.rs',*sorted((base/'user_client').glob('*.rs'))]
source={str(p.relative_to(R)):p.read_text() for p in files}
rows=[]
for name,s in source.items():
 for i,line in enumerate(s.splitlines(),1):
  if re.search(r'\b(?:format|println|eprintln|print)!|serde_json::|\.to_string\(\)|\b(?:wallet_fd_path|render_json|pubkey_text|parse_request|print_json|json_string|json_array|json_bool|json_number|json_object|json_into_array|hex)\(',line):
   rows.append(dict(source=name,line=i,text=line))
root=source['tools/r1-cost-probe/src/bin/user_client.rs'];wallet=source['tools/r1-cost-probe/src/bin/user_client/wallet.rs'];plan=source['tools/r1-cost-probe/src/bin/user_client/plan.rs'];diag=source['tools/r1-cost-probe/src/bin/user_client/diagnostics.rs']
assert 'let fd=i32::try_from(crate::public_field(q,"wallet_bytes_fd").as_u64()' in wallet
assert wallet.index('crate::wallet_fd_path(fd)')<wallet.index('crate::wallet_read_record(&mut channel)')
assert 'fn wallet_fd_path(fd:i32)->String{format!("/proc/self/fd/{fd}")}' in root
assert 'let rendered=render_json(&plan::run(&q)?);print_json(rendered)' in root
assert 'fn render_json(value:&Value)->String{format!("{}",value)}' in root
assert "text.push('\\n')" in root and 'output.write_all(text.as_bytes())' in root
assert 'println!' not in root
assert 'parse_request(&s)?' in root and 'serde_json::from_str(text).map_err(err)' in root
assert 'fn pubkey_text(value:solana_program::pubkey::Pubkey)->String{value.to_string()}' in root
assert 'let started=Instant::now();let secrets=super::wallet::read(q)?' in plan
assert 'serde_json::Number::from_f64(started.elapsed().as_secs_f64())' in plan
assert 'super::wallet::retain(dir,&secrets.record)?' in plan
assert 'file.write_all(record)' in wallet
assert 'write_all(b"client error\\n")' in diag and 'write_all(b"client panic\\n")' in diag
out_fields=re.findall(r'out.insert\("([^"]+)"\.to_owned\(\),(.*)\);',plan)
assert len(out_fields)==15,len(out_fields)
# Same exact source expressions are recorded, never presumed public merely
# because a value is eventually printed.
x=dict(evidence_class='Script-checked source anchors plus manual structural data-flow classification; not a whole-client Lean refinement',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),sources={n:hashlib.sha256(s.encode()).hexdigest() for n,s in source.items()},calls=rows,output_fields=[dict(key=k,expression=v) for k,v in out_fields],findings=[
 dict(id='FMT-STDOUT-WRITER',call='user_client::render_json(&plan::run(&q)?) -> String; print_json(String) raw write',status='FORMATTING STAGE REPAIRED: render_json writes to String; byte emission is separate fallible I/O. Its prefix/failure/abort and changed allocation/write-grouping effects remain a native P obligation',source='formatting-source-d561.json'),
 dict(id='FMT-ELAPSED-ARG',call='serde_json::Number::from_f64(started.elapsed().as_secs_f64())',status='clock read spans wallet decode, witness-dependent membership selection, compilation and prover; not derived from public request; witness-independent honest-run law unproved',retained='whole-client L1/L2/L3 and observation; no new T field'),
 dict(id='FMT-TRANSCRIPT-ARGS',call='stdout Value plus public-key ToString/number conversions selected by result.attempts',status='pubkey_text(selected key/marker/lane/page), number(result.attempts/proof.len), hex(instruction data), statement/proof file serializers and render_json(out) consume prover/witness-derived protocol outputs. Their public/simulated status needs the existing E1/E2, retry and public-transcript laws; it is not proved by declaring printed data public or by renderer congruence.'),
 dict(id='FILE-RECOVERY-SECRET',call='wallet::retain(dir,&secrets.record) -> file.write_all(record)',status='DEFINITE SECRET ARGUMENT: identity binary serialization of the 212-byte wallet record. Not public or witness-independent. Retained mode-0600 file in mode-0700 directory; whether this private sink is excluded from observer-visible bytes is an unproved boundary. Never delete it to hide the finding.')],
 discharged_local_laws=[dict(call='wallet format!("/proc/self/fd/{fd}")',arguments='fd is a projection/conversion solely of public q.wallet_bytes_fd, checked before any private record read',writer='Rust String::fmt::Write push_str then Ok; allocation abort retained',model='PV_UC_ReadyEntry.wallet_fd_path : I32 -> Result String is an explicit operation parameter; pure native String rendering, no text semantics or Unit carrier evidence',proof='PV_UC_FinalPublicFormatting.extracted_fd_formatter_public')],
 limits=['Actual wallet_fd_path, pubkey_text, parse_request and render_json preserve their typed operands. Distinct effect records may read different private records; shared-formatter binding laws are explicit hypotheses. Their congruence proofs use no formatting contents or Unit carrier semantics; native association and publicness of the entire rendered Value remain explicit.', 'The final String-rendering entry has 22 carrier and 104 operation parameters; native association remains explicit for I/O, clock, prover and entropy as well as formatting.', 'No endpoint premise is removed. No field is added to the capped T list.'])
(R/'evidence/pv-uc-20261029/formatting-flow-d561.json').write_text(json.dumps(x,indent=2)+'\n')
