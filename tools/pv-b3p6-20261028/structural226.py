"""Fail-closed source inventory for a structural K-1 substitute CANDIDATE.
A successful preflight is not native equality or a row closure: outstanding
value/Vec-composition laws are explicitly retained in the output.
"""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];D=R/'evidence/pv-b3p6-20261028'
p='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
base='5fa2cc6781d436cf346e630850f8aaac2f64ef93'
s=(R/p).read_text();frozen=subprocess.check_output(['git','show',base+':'+p],cwd=R).decode()
assert s==frozen,'shipped source differs from candidate'
def body(src,anchor):
 start=src.index(anchor);a=src.index('{',start);depth=1;i=a+1
 while depth:
  if src[i]=='{':depth+=1
  elif src[i]=='}':depth-=1
  i+=1
 return src[a+1:i-1]
def tokens(src):
 src=re.sub(r'//[^\n]*|/\*.*?\*/','',src,flags=re.S)
 return re.findall(r'\w+|::|>=|->|[^\s]',src)
b=body(s,'pub fn public_bytes(self) -> Result<Vec<u8>, Error>')
field=body(b,'fn fields(')
assert tokens(field)==tokens('''for value in values {
 if value.0 >= aspis_core::field::P { return Err(Error::Public); }
 out.extend_from_slice(&value.0.to_le_bytes()); } Ok(())''')
front=body(b,'fn frontier(')
assert tokens(front)==tokens(''.join(f'fields(out, &values[{i}])?;' for i in range(20))+'Ok(())')
main=b[b.index('let p = self.semantic();'):]
args=re.findall(r'fields\(&mut out,\s*([^\n]+)\)\?;',main)
assert args==['&p.anchor','&p.nullifier','&[p.asset_id]','&value','&p.change','&[M31(value)]','&after.next_root'],args
assert re.findall(r'frontier\(&mut out, ([^\n]+)\)\?;',main)==['&source.frontier','&after.next_frontier']
steps=['out.push(match p.variant','fields(&mut out, &p.anchor)?;','fields(&mut out, &p.nullifier)?;',
 'fields(&mut out, &[p.asset_id])?;','out.push(u8::from(p.recipient.is_some()));',
 'if let Some(value) = p.recipient','fields(&mut out, &p.change)?;',
 'out.push(u8::from(p.withdrawal_amount.is_some()));','if let Some(value) = p.withdrawal_amount',
 'out.extend_from_slice(&source.next_pair_index.to_le_bytes());','frontier(&mut out, &source.frontier)?;',
 'fields(&mut out, &after.next_root)?;','frontier(&mut out, &after.next_frontier)?;','Ok(out)']
positions=[main.index(x) for x in steps];assert positions==sorted(positions)
ref=R/'tools/pv-b3p6-20261028/reference226.rs'
pre=json.loads((D/'preflight226v3.json').read_text())
assert hashlib.sha256(ref.read_bytes()).hexdigest()==pre['reference_sha256']
record=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 candidate=base,native_source=p,native_sha256=hashlib.sha256(s.encode()).hexdigest(),
 native_public_bytes_sha256=hashlib.sha256(b.encode()).hexdigest(),reference_sha256=pre['reference_sha256'],
 native_field_order=args,native_frontier_rows=list(range(20)),native_main_call_order=steps,
 source_checks_passed=True,native_link_credit=False,row_closed=False,
 evidence_class='structural (K-1 substitute) CANDIDATE; incomplete',
 checked_components=['owned projection and carrier roundtrip','four canonical checks equal one guarded word',
 'word and index endian equality','every-input outer-result termination','both-variant installed nonvacuity',
 'exact successful1427/1455 output lengths','261 other callback frames','finite same-input native/emission fixtures'],
 retained_obligations=['complete byte-value/layout correspondence for every region',
 'chunk flatten/take value composition over the same input','native Vec append/growth structural composition',
 'whole-function native binding; paired mitigated Kani invocation12 timed out'],
 warning='Syntax/order/source pins only. Checked component details and receipts are in row-status.json; this preflight does not establish any retained obligation.')
(D/'structural226-candidate.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'source_checks_passed':True,'native_link_credit':False,'retained_obligations':len(record['retained_obligations'])}))
