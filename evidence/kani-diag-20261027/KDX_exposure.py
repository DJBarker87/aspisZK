from pathlib import Path
import json
E=Path(__file__).resolve().parent
rows=json.loads((E/'KDX_HARNESS_SCAN.json').read_text());out=[]
# Manual adjudication of every conservative call-name hit with a memory primitive.
actual={
'LPa_K004':('16 u8; reference loop32',False,'Reached byte copy; bound sufficient.'),
'LPa_K005':('16 u8 in callee; reached copy length0',True,'Alignment rejection precedes the copy. No exposure on admitted domain; K023 PASS.'),
'LPa_K007':('16 u8 in callee; reached copy length0',True,'Length rejection precedes the copy. No copy exposure on admitted domain; K024 TIMEOUT, no new pass.'),
'LPa_K015':('32 u8',False,'Reached fixed byte copy; sufficient bound; no new replay result.'),
'LPl_K015':('16 u8',False,'Reached byte copy; sufficient bound; replay setup failed before verification.'),
'LPm_K001':('64 K elements =1024 bytes',True,'Element bound66 is sufficient; byte count exceeds bound. K022 PASS at1025; typed-copy audit retained because adequate unwind does not cure diagnostic.'),
'LPm_K003':('prefix<=1720 u8; append16',False,'All explicit copies and possible realloc prefix fit1740. No additional replay.'),
'LPm_K004':('prefix<=1704 u8; append32',False,'All copies fit1740. K028 PASS at1769.'),
'LPm_K005':('prefix<=1732 u8; append4',False,'All copies fit1740. No additional replay.'),
'LPn_K001':('16 u8',False,'Reached byte copy. K027 PASS at33.'),
'LPn_K010':('16 u8',True,'Reached copy16>10 populates ignored high half; possible loss of suffix variation under model discrepancy. K021 PASS at33; this is not a model-fidelity theorem.'),
'LPb_K016':('append32 u8 x6; realloc up to128 bytes',True,'Explicit copy fits34; potential realloc copy128>34. Not replayed; historical graph revalidation remains OPEN.'),
'LPe_K005':('append32 u8 x6; realloc up to128 bytes',True,'Explicit copy fits34; potential realloc copy128>34. Model exposure unresolved; not replayed.'),
'LPe_K015':('two copies8 u8',False,'Capacity1768 avoids realloc; sufficient bound18.'),
'LPe_K016':('clone16; appends32; realloc up to96 bytes',True,'Explicit copy fits34; possible realloc96>34. Model exposure unresolved; not replayed.'),
'LPe_K017':('copy32/4; realloc up to128 bytes',True,'Explicit copies fit90; possible realloc128>90. Model exposure unresolved; not replayed.'),
'LPe_K018':('prefix32; append32/16; realloc64 bytes',True,'Explicit copies fit34; possible realloc64>34. Model exposure unresolved; not replayed.'),
'LPe_K019':('append16 x14; realloc up to128 bytes',True,'Explicit copies fit34; possible realloc128>34. Model exposure unresolved; not replayed.'),
'LPf_K027':('initial1736; append32 u8',False,'Possible realloc1736 fits1738; no additional replay.'),
'LPg_K011':('16 u8',False,'Reached byte copy; bound18 sufficient; initial replay setup failed.'),
'LPg_K012':('16 u8',False,'Reached byte copy; bound18 sufficient; initial replay setup failed.'),
'LPh_K018':('16 u8',False,'Reached byte copy; bound18 sufficient; initial replay setup failed.'),
'LPh_K019':('16 u8',False,'Reached byte copy; K025 PASS at33.'),
'LPh_K020':('16 u8',False,'Reached byte copy; K026 PASS at33.'),
'LPh_K021':('16 u8',False,'Reached byte copy; bound18 sufficient; initial replay setup failed.'),
'LPi_K012':('prefix<=1720; stub copy16 u8',False,'All copies fit1740; no additional replay.'),
'LPi_K013':('prefix<=1704; append32 u8',False,'All copies and stub32-iteration loop fit1740; no additional replay.'),
'LPi_K017':('body1736; replacements32; append32',False,'All copies fit1740; no additional replay.'),
'LPi_K018':('body1736; replacements32; append32',False,'All copies fit57609; no additional replay.'),
'NBE_K005':('callee sibling32 u8; reached copy0',True,'n==0 or n>16 rejects before loops and copy; no exposure on admitted domain; no replay.'),
'NBH_K029':('4,32,32,32,8,32 u8',False,'No finite unwind supplied; builtin fixed stores; no small-bound/disabled-check match. No replay.')}
for a in ['LPi_K005','LPi_K006','LPi_K007','LPi_K008','LPi_K009','LPi_K010']:
 actual[a]=('8 u8 in CM31 byte stub',False,'Stub copy8 fits18; target16-byte serializer uses two such calls. No additional replay.')
for r in rows:
 a=Path(r['receipt']).parent.name
 if not any(m['copies'] for m in r['marks']):continue
 length,flag,verdict=actual.get(a,('No reached syntactic copy from this hit',False,'Call-name overapproximation only: unrelated overloaded/helper names or field identifiers. Selected body does not call the reported copying helper. Not a small-bound memory-copy match.'))
 out.append(dict(id=a,harness=r['harness'],receipt=r['receipt'],bound=r['bound'],unwinding_disabled=r['disabled'],copy_or_loop_length=length,review_flag=flag,verdict=verdict,command=r['command']))
assert not any(r['disabled'] for r in rows)
(E/'KDX_EXPOSURE.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['| Harness / receipt | Unwind; checks | Copy or loop length | Exposure verdict |','|---|---|---|---|']
for r in sorted(out,key=lambda x:x['id']):
 label=f"[{r['id']}](../../{r['receipt']}) `{r['harness']}`"
 lines.append('| '+label+' | '+str(r['bound'] if r['bound'] is not None else 'no finite bound')+'; enabled | '+r['copy_or_loop_length']+' | '+r['verdict']+' |')
(E/'KDX_EXPOSURE_TABLE.md').write_text('\n'.join(lines)+'\n')
# Index includes every PASS, not only rows with potential memory operations.
index=[dict(receipt=r['receipt'],harness=r['harness'],bound=r['bound'],unwinding_disabled=r['disabled'],source=r['source'],operation_candidates=r['marks'],command=r['command']) for r in rows]
(E/'KDX_ALL_PASS_SCAN.json').write_text(json.dumps(index,indent=2)+'\n')
print(len(rows),'passes indexed;',len(out),'memory candidates;',sum(x['review_flag'] for x in out),'review flags')
