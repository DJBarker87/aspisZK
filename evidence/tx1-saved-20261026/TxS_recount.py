"""Reviewed law-family correspondence, using the Rc2 ledger's atomic leaves,
quantified families, identical witnesses/guards and shared-dictionary dedup.
This renders the reviewed change; it is not a logical discharge checker.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[1]
BASE=ROOT/'evidence/recount2-20261026/Rc2_premises.json'
x=json.loads(BASE.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def statement(name):
 s=(ROOT/'lean'/f'{name}.lean').read_text()
 return s[s.index('theorem deployed'):s.index(' := by',s.index('theorem deployed'))]
norm=lambda s:re.sub(r'\s+','',s)
assert norm(statement('Rc2_Top').replace('Rc2_Result.Outcome','TxS_Result.Outcome'))==norm(statement('TxS_Top'))
assert norm(statement('Rc2_Top'))==norm(statement('TxS_LegacyTop'))
raw=(ROOT/'lean/TxS_RawFinish.lean').read_text().split('theorem of_typed')[0]
assert 'tx1_saved' not in raw and '(i : SourceInputs)' not in raw and '(tr : RawCutTranscriptRun.ErasedPrefix)' not in raw
carriers=(ROOT/'lean/TxS_Carriers.lean').read_text()
for structure in ['Prefix','Metadata']:
 fields=carriers.split('structure '+structure+' where',1)[1].split('\n\n',1)[0]
 assert 'initFits' not in fields and 'Functional' not in fields and 'MatchingSupport.Data' not in fields
assert '(LiteralMatchingData.read rs).getD zeroData' in carriers
assert 'TxS_Encoding.Model' in (ROOT/'lean/TxS_ContSource.lean').read_text()
assert 'TxS_Encoding.Facts' in (ROOT/'lean/TxS_Result.lean').read_text()
log=(OUT/'TxS_098/stdout.log').read_text()
for target in ['Rc2_Top.deployed','TxS_Top.deployed','TxS_LegacyTop.deployed']:
 assert '@AspisR1.'+target in log
assert json.loads((OUT/'TxS_098/receipt.json').read_text())['exit_status']==0
removed={
'N115':('TxS_Writer.saved; TxS_Reader.saved; TxS_Transfer.prepare; TxS_Query.twelve; TxS_FinishProof.strengthen; TxS_Pair.accepted; TxS_Top.deployed',
'Complete physical writer/reader body on SAME run; same source accumulator identified with model ten by original authentication/read/preparation gates. Finish consumes only derived query and accumulator fields; no arbitrary Context equation assumed.'),
'L151':('TxS_Carriers.functional; TxS_DecoderSelected.selected_functionals; TxS_Decoder.functional_origin; TxS_RawTen; TxS_RawFinish; TxS_Top.deployed',
'Original arbitrary law-bearing MatchingSupport.Data/SourceInputs binders replaced by decoder-produced data. The exact selected semantic functionals or failed-read zero maps are constructed, and Par addition laws instantiated there. Both-direction successful-read transport preserves every original model case. Not a new native arithmetic result.'),
'L152':('TxS_Carriers.functional; TxS_Decoder.functional_origin; TxS_Top.deployed',
'Same concrete decoder-instance replacement for scalar multiplication; no arbitrary functional carrier or map_smul premise.'),
'L153':('TxS_Carriers.prefix_erase; TxS_RawPublic.of_typed/to_typed; TxS_RawTen.of_typed/to_typed; TxS_RawFinish.of_typed/to_typed; TxS_Top.deployed',
'Raw public bytes/tag/rounds contain no initFits proof. Bound constructed by total conversion; every original typed prefix is preserved exactly. SAME source-public bound is retained as a derived output. ByteProver was already raw Submission at Rc2; no adversary restriction added.')}
rows=[];diff=[]
for old in x['rows']:
 r=dict(old)
 if r['id'] in removed:
  th,why=removed[r['id']]
  assert r['scope']=='actual antecedent' and r['owner']=='lead' and r['classification']=='P'
  diff.append({**r,'status':'removed by TxS','checked_result':th,'audit_reason':why})
 else:rows.append(r)
assert {r['id'] for r in diff}==set(removed)
def counts(rr):
 return dict(rows=len(rr),classes=dict(Counter(r['classification'] for r in rr)),owners=dict(Counter(r['owner'] for r in rr)),by_owner={o:dict(Counter(r['classification'] for r in rr if r['owner']==o)) for o in ['lead','session A','external']})
def summaries(rr):
 ss={s:counts([r for r in rr if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}
 ss['all retained audit rows']=counts(rr)
 ss['deduplicated actual plus non-alias deployment']=counts([r for r in rr if r['scope']!='deployment alias'])
 return ss
before=summaries(x['rows']);after=summaries(rows)
assert before['actual antecedent']['classes']=={'T':82,'P':171}
assert after['actual antecedent']['classes']=={'T':82,'P':167}
assert after['actual antecedent']['by_owner']['lead']=={'P':19}
y=dict(target='AspisR1.TxS_Top.deployed',baseline_target='AspisR1.Rc2_Top.deployed',method='Rc2 atomic leaves and quantified law families; same witnesses/guards; shared dictionary dedup; reviewed correspondence rendered mechanically',baseline_sha256=sha(BASE),removed=diff,added=[],retained_rows=rows,before=before,after=after,notes=['Inherited security-only slice82T+166P ->82T+162P; five Rc2 protection guards unchanged.','No source arithmetic, new runtime trust, probability/frozen3 headline, global joint non-vacuity or release closure claimed.','TxS_Selected.same_run is the complete Context/Prepared/body theorem on the explicitly installed frozen3 circle dictionary, not a new guard of general TxS_Top.'])
(OUT/'TxS_premises.json').write_text(json.dumps(y,indent=2)+'\n')
lines=['# Recount against actual Rc2_Top','', 'Removed: N115, L151, L152, L153. Added: none.','', '| Scope | Before T/P | After T/P |','|---|---|---|']
for k in before:
 b=before[k]['classes'];a=after[k]['classes'];lines.append(f"| {k} | {b.get('T',0)}/{b.get('P',0)} | {a.get('T',0)}/{a.get('P',0)} |")
lines+=['','Actual lead P:23 ->19. Session A/external unchanged. Not a security percentage.','', 'The complete original root statement is recovered by TxS_LegacyTop.deployed; its statement is byte-normalized equal to Rc2_Top. Root binders and other conclusions are unchanged. N115 is genuinely removed; three intrinsic carrier-law families are constructed at the decoder instance instead of supplied in arbitrary model carriers. Both directions of raw/typed continuation transport are checked. No law-containing record bundles replace them.','', 'Non-vacuity: exact surjectivity for all original typed transcripts and successful matching inputs, inhabited local writer domain, and SAME-source accepted/non-reject-all input under original history/P2Prime. Joint global runtime/crypto/experiment inhabitance remains open.']
(OUT/'TxS_LEDGER_DELTA.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({'removed':list(removed),'actual':after['actual antecedent'],'dedup':after['deduplicated actual plus non-alias deployment']},indent=2))
