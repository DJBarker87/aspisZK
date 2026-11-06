from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
x=json.loads((E/'NKR_SumFinish_TRANSCRIPTION.json').read_text());y=json.loads((E/'NKR_SumPattern_TRANSCRIPTION.json').read_text());s=(E/'NKR_SumSplit_native.rs.txt').read_text()
def body(t,name):
 p=t.index('fn '+name+'(');p=t.index('{',p);q=p+1;d=1
 while d:d+=(t[q]=='{')-(t[q]=='}');q+=1
 return t[p+1:q-1]
def closure(t,name):
 p=t.index('let '+name+':')if'let '+name+':'in t else t.index('let '+name+' :');p=t.index('|index|',p);p=t.index('{',p);q=p+1;d=1
 while d:d+=(t[q]=='{')-(t[q]=='}');q+=1
 return t[p+1:q-1]
norm=lambda t:re.sub(r'\s+','',t)
t=x['translated'];a=t.index('values[group]');b=t.index('coordinate += count;',a)+len('coordinate += count;');arith=t[a:b].replace('NKR_finish_add','NKR_ss_add').replace('NKR_finish_sum','NKR_ss_sum')+'(values,weights,coordinate)'
checks={'tag':norm(closure(t,'tag_values').replace('NKR_finish_tag','NKR_ss_tag'))==norm(body(s,'NKR_ss_tag_cell')),'weight':norm(closure(t,'weight_values'))==norm(body(s,'NKR_ss_weight_cell')),'low':norm(closure(t,'lows'))==norm(body(s,'NKR_ss_low_cell')),'arithmetic':norm(arith)==norm(body(s,'NKR_ss_arithmetic'))}
assert all(checks.values()),checks
# Pattern split at its pure scalar-product child. The receiver read commutes
# over that CLOSED field call's empty mutable footprint; no output is assumed.
pt=y['translated_pattern'];head=pt[:pt.index('pattern_selectors[output]')];prod=head+'(output,NKR_ss_mul(scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET+coordinate],low,l))'
checks['pattern_product']=norm(prod)==norm(body(s,'NKR_ss_product'))
assert checks['pattern_product'],checks
row=dict(revision=x['revision'],source=x['source'],source_sha256=x['source_sha256'],harness_sha256=hashlib.sha256(s.encode()).hexdigest(),checks=checks,original_batch=x['original'],original_pattern=y['original_pattern'],segments={n:body(s,n)for n in ['NKR_ss_tag_cell','NKR_ss_weight_cell','NKR_ss_low_cell','NKR_ss_arithmetic','NKR_ss_product','NKR_ss_write']},pattern_write_association='Scalar add logging/write window: actual output and product from preceding product segment; exact one-cell update, full arbitrary-coordinate frame, coordinate+1. Receiver may be read before/after pure field product because its CLOSED mutable footprint is empty.',retired=['NKR_K038','NKR_K040'],representative_restriction=False)
(E/'NKR_SumSplit_TRANSCRIPTION.json').write_text(json.dumps(row,indent=1));print('Five split batch/pattern windows retain exact source operands/control and universal frames')
