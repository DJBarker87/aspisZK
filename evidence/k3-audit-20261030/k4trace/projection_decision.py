from pathlib import Path
import json,sys,lzma
E=Path(__file__).resolve().parent
credit,ident=sys.argv[1:];D=E/'host'/ident
summaries=[];locations=set();actual=[]
for p in sorted(D.glob('cbmc-*.json*')):
 if '-command.json'in p.name or p.suffix=='.sha256':continue
 cmd=json.loads((D/(p.name.removesuffix('.xz').removesuffix('.json')+'-command.json')).read_text());goto=next(x for x in cmd['argv']if x.endswith('.out'))
 fs=[f for x in json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes()) for f in x.get('result',[])if f.get('status')=='FAILURE'and f.get('sourceLocation',{}).get('propertyClass')!='reachability_check']
 if '_wrong_'not in goto:assert not fs;continue
 assert len(fs)==1
 f=fs[0];line=f['sourceLocation']['line'];assert line==('44'if'_wrong_frame'in goto else'42');locations.add(line)
 t=f['trace'];vals={s['lhs']:s.get('value',{}).get('data')for s in t if s.get('stepType')=='assignment'and s.get('lhs')in ['index','query','byte_index','byte_query','lane']}
 operands=[{'step':i,'lhs':s.get('lhs'),'value':s.get('value')}for i,s in enumerate(t)if s.get('sourceLocation',{}).get('file')=='src/indexed.rs'and s.get('sourceLocation',{}).get('line')==line and s.get('stepType')=='assignment']
 summaries.append({'trace_file':str(p.relative_to(E)),'goto':goto,'intended_mutation':'frame XOR1'if line=='44'else'value XOR1','location':f['sourceLocation'],'logical_state':vals,'terminal_assignments':operands,'full_trace_steps':len(t)})
 actual.append('line '+line+': index='+str(vals.get('index'))+', query='+str(vals.get('query'))+', byte_index='+str(vals.get('byte_index')))
assert locations=={'42','44'}
assert 'Complete - 1 successfully verified harnesses, 2 failures, 3 total.' in (D/'output.log').read_text()
(D/'control-assessment.json').write_text(json.dumps(summaries,indent=2)+'\n')
d={'credit':credit,'classification':'RESTORE','positive':ident,'positive_verdict':'SUCCESSFUL; original positive passes (1 pass / 2 intended controls fail)','control':ident,'control_verdict':'Both original controls FAIL at intended assertions (value XOR1 / frame XOR1)','location':'src/indexed.rs:42 and :44','source_sha256':'073fd146dc0eab518888d55f24bda3623e1abbad8d2ebcbc345af05fc91b6e49','reason':'The positive passes and both controls fail only their intended non-probe assertions. Value failure is result[lane] versus bits[lane]^1 at line 42; frame failure is framed[lane] versus expected^1 at line 44. Full raw traces and numbered terminal assignments are retained in control-assessment.json and trace-excerpt.json. Logical offsets stay in u128; physical destination offsets are only 0 or 1 in the frozen two-place projection. Thus these failures are the deliberate XOR mutations, not 48-bit aliasing. Recorded control states: '+'; '.join(actual)+'.','trace_excerpt':'host/'+ident+'/control-assessment.json','full_trace':[x['trace_file'] for x in summaries],'scope':'Segregated logical-offset/two-place projection only; original ptr.add/allocation/OWNER association stays OPEN.'}
(E/(credit+'.json')).write_text(json.dumps(d,indent=2)+'\n');print(credit,'RESTORE')
