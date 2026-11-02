"""Check the source anchors used by the D561 formatting/data-flow review."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];base=R/'tools/r1-cost-probe/src/bin'
files=[base/'user_client.rs',*sorted((base/'user_client').glob('*.rs'))]
source={str(p.relative_to(R)):p.read_text() for p in files}
rows=[]
for name,s in source.items():
 for i,line in enumerate(s.splitlines(),1):
  if re.search(r'\b(?:format|println|eprintln|print)!|serde_json::|\.to_string\(\)',line):
   rows.append(dict(source=name,line=i,text=line))
root=source['tools/r1-cost-probe/src/bin/user_client.rs'];wallet=source['tools/r1-cost-probe/src/bin/user_client/wallet.rs'];plan=source['tools/r1-cost-probe/src/bin/user_client/plan.rs'];diag=source['tools/r1-cost-probe/src/bin/user_client/diagnostics.rs']
assert 'let fd=i32::try_from(crate::public_field(q,"wallet_bytes_fd").as_u64()' in wallet
assert wallet.index('format!("/proc/self/fd/{fd}")')<wallet.index('channel.read_exact(&mut record)')
assert 'println!("{}",plan::run(&q)?)' in root
assert 'serde_json::from_str(&s)' in root
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
 dict(id='FMT-STDOUT-WRITER',call='user_client::run println!("{}", plan::run(&q)?)',status='String-writer exemption does not apply to actual stdout writer; preserve prefix/failure/abort effects',source='formatting-source-d561.json'),
 dict(id='FMT-ELAPSED-ARG',call='serde_json::Number::from_f64(started.elapsed().as_secs_f64())',status='clock read spans wallet decode, witness-dependent membership selection, compilation and prover; not derived from public request; witness-independent honest-run law unproved',retained='whole-client L1/L2/L3 and observation; no new T field'),
 dict(id='FMT-TRANSCRIPT-ARGS',call='stdout Value plus public-key ToString/number conversions selected by result.attempts',status='protocol output arguments require the existing public-transcript and retry laws; no proof that those native laws hold is supplied by pure renderer congruence'),
 dict(id='FILE-RECOVERY-SECRET',call='wallet::retain(dir,&secrets.record) -> file.write_all(record)',status='direct secret bytes, not formatting; retained private recovery file; must not be classified as public observer data or deleted; OS permission/observer boundary remains explicit')],
 discharged_local_laws=[dict(call='wallet format!("/proc/self/fd/{fd}")',arguments='fd is a projection/conversion solely of public q.wallet_bytes_fd, checked before any private record read',writer='Rust String::fmt::Write push_str then Ok; allocation abort retained',model='PV_UC_PublicFormatting.Renderers.fdPath : Int -> String; deterministic renderer parameter, no text semantics or Unit carrier evidence',proof='PV_UC_PublicFormatting.walletPath_same_public')],
 limits=['Pure renderer fields are explicit parameters. They are not installed as arbitrary global external definitions.', '25 external carrier templates and 119 operation templates remain uninstalled; their native bindings include I/O, clock, prover and entropy, not just formatting.', 'No endpoint premise is removed. No field is added to the capped T list.'])
(R/'evidence/pv-uc-20261029/formatting-flow-d561.json').write_text(json.dumps(x,indent=2)+'\n')
