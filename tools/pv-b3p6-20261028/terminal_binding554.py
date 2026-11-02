"""Bind the actual no-optimized-terminal feature selection, not the inactive copy."""
from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ns={};exec(compile(Path('tools/pv-b3p6-20261028/std_resolve_d540.py').read_text().split('indices={}')[0],'<parser>','exec'),ns)
tokens,index=ns['tokens'],ns['index'];p=Path('crates/aspis-r1-cost-probe/src/host_terminal.rs');pins=json.loads((D/'resume17/deployed-source-pins.json').read_text());assert sha(p)==pins[str(p)]
old=json.loads((D/'resume9/body-inventory.json').read_text());original={r['key'].split('#')[0]:r['source']for r in old['bodies']if r['family']=='terminal'and r['source']}
items={r['name']:r for r in index(p.read_text())}
features=json.loads((R/'reference-projected/inputs.json').read_text())['features'];host=next(n for n in features if n['name']=='aspis-r1-cost-probe');assert 'optimized-terminal'not in host['features'];assert 'ct-host-prover'in host['features']
def matching(t,i):
 pairs={'[':']','(':')','{':'}'};end=pairs[t[i]];depth=1;j=i+1
 while depth:
  if t[j]==t[i]:depth+=1
  elif t[j]==end:depth-=1
  j+=1
 return j
def selected(t):
 out=[];i=0
 while i<len(t):
  if t[i:i+3]==['#','[','cfg']:
   e=matching(t,i+1);cfg=t[i:e]
   assert cfg in [tokens('#[cfg(not(feature="optimized-terminal"))]'),tokens('#[cfg(feature="optimized-terminal")]')],cfg
   enabled='not'in cfg
   if t[e]=='{':stop=matching(t,e)
   else:
    stop=e
    while t[stop]!=';':
     if t[stop]in ['[','(','{']:stop=matching(t,stop)
     else:stop+=1
    stop+=1
   if enabled:out+=t[e:stop]
   i=stop
  else:out.append(t[i]);i+=1
 return out

def historical_body(t):
 text=' '.join(t[t.index('{'):])
 for op in ['::','+=','-=','*=','<<','>>','..','<=','>=','==','!=','->','=>','&&','||']:
  text=text.replace(' '.join(op),op)
 return tokens(text)

maps={
'add_path_lanes':('path_dispatch_source554','path_dispatch_source_link554',[
('sum_high57..63','source_sum_interval11','Same ZERO-seeded ascending high slice sum; sum source law and exact interval bindings reused.'),
('low1+5+9+13 then nodes.mul','path_dispatch_source554 prefix','Exactly four reads, three left-associated adds, one mul in source order; no field reassociation.'),
('cfg literal path','native_path15','Feature graph omits optimized-terminal. The complete literal source is already bound by PATH-SOURCE-D546 and native_path_binding15. Inactive factored kernel is not substituted or credited.'),
('add_preweighted start32','native_preweighted15','Exact seventeen values and updated packed return; total direct extraction plus source macro law retain every packed write.')]),
'add_value_lanes':('value_scaling_source11','value_source_link554',[
('value selectors rows16*63+0,2,4; range selector','value_direct_stage9_00..07','Source row expressions and ZERO-seeded three adds retained. First three while loops each visit0..9, filling range0..9,10..19,20..29 from z/succ/xor12. Every read, square, subtraction and direct write has ValueRead/ValueDigit/ValueFrame/ValueSequence laws in resumes9..11; no reassociation.'),
('reconstruct three10-bit values; range30,31,32','value_direct_stage9_00..07 suffix','Historical paired Kani reconstruct10 association is reused under k-double-prime. Reconstruction shifts10 and20 and add order preserved, then z10 subtraction and succ/xor10 copies.'),
('cfg not optimized scaling33 entries','scale_frame11 loop at33','All33 values are read, multiplied by range_selector on the left, written back in order. Iterator-mut restoration represented by scale_cell11/scale_frame11 and ScaleLoopFrame11; model retains both selector and complete range. No iterator backward result dropped.'),
('preweighted range start49','value_direct_stage9_14','Full scaled range33 passed to bound total add_preweighted source row; full updated packed retained before conservation reads.'),
('conservation row16*63+6 and two residuals','value_direct_stage9_14 suffix','First z0-z1-z2 then succ0-succ1; selector multiplication in source order, array2, preweighted start82 using the updated packed. Inactive shared-selector kernel remains distinct.')]),
'semantic_initial_and_absorption':('sum_context11_semantic_initial_and_absorption source_sum_interval11','initial_absorption_source_link554',[
('sum nodes ranges4..25,33..57','source_sum_interval11 twice','Second interval starts from the first returned sum. Both direct source range bindings and complete Result preserved.'),
('first_common high0,1,25,30 and variant high27,28,29','sum_context11 prefix','Source initial_variant_selectors call and returned four selectors in original order; named variant helper source row remains separate.'),
('low0 full and rate; prepare full, full_or_rate','sum_context11 prepared prefix','Source add/mul order preserved. Nominal prepared field carrier and primitive source relation remain separately named; no field identity assumed.'),
('qm31_array initial16','output0..output16 and initial_lane227','Source macro is the checked increasing sixteen-cell schedule, each reads openings.z[lane] then chooses full_or_rate belowRATE8 or full otherwise, performs prepared multiplication, and stores that cell. Source grammar/macro/branch laws from resumes9,12,15 retained.'),
('note/domain/length; initialRATE andRATE+1 corrections','output17,output18','Exact DOMAIN_OWNER_KEY/NOTE/NULLIFIER and lengths8/18/16; same low0 multiplication then subtraction. Each update restored before the following index read.'),
('chunk_eight high0,1,2,25,26,30,31 and chunk_two3,32','sum_context11 final selector prefix','Original left association, then respective private variant selector additions, and low12 read preserved.'),
('cfg literal absorption','absorption_lanes_literal','Actual no-optimized graph selects the directly extracted literal16 array source law. Same low12,fixed,chunk_two,chunk_eight,nodes,z argument order; returned pair(output18,absorption). Inactive factored kernel not claimed bound.')])}
maps['semantic_packed']=('semantic_source554','semantic_source_link554',[
('ZERO packed24 then schedule,path,value,occupancy','context12_preweighted_reference_terminal_semantic_packed','Exactly four source calls in order, passing every restored packed array into the next. Source helper relations are separate named rows, never replaced by a zero or success-only result.'),
('selected public-digest literal branch','public_digest_lanes then native_preweighted15 at84','Metadata excludes optimized-terminal. Same complete public/openings/selectors arguments, eight digest lanes, and restoration before asset read. Direct digest and preweighted source laws are reused.'),
('asset difference z1-lift(asset_id)','semantic context asset prefix','Same field read, raw M31 lift, subtraction and reuse of pure immutable difference; no assumption about canonicality or zero.'),
('input/output/private selectors and withdrawal scalar','semantic context row expressions','Evaluate rows2*16+12,31*16+12,28*16+12, then unwrap_or0 and row16*63+2 and z10-lift(amount), preserving evaluation order and each multiplication.'),
('scalar_lanes then preweighted92','semantic context suffix','Variant and is_some flag feed the same scalar source helper; all returned scalar lanes passed intact to the final preweighted call using updated packed5, then full packed state returned.')])
maps['composition_parts']=('composition_source554','composition_source_link554',[
('invalid withdrawal amount match','composition_source554 first match','None yields false; Some0 short-circuits true; otherwise compute1<<30 and compare amount>=upper. Early Err InvalidPublicAmount before transition or selected claims, with the original Option retained in public.'),
('validate_transition(public)?','transition and CoreOpsTry.branch','Identical public record and error propagation. Historical paired transition Kani association retained under k-triple-prime; Break returns the same residual without entering later computations.'),
('three sixteen-element openings macros','select_c1_227 claims0,1,2','qm31_array schedule reads every selected claim in column order, constructing z,succ_z,xor12_z independently. Source helper spans and actual flattened84 carrier/provenance remain named; no all-zero claims substitution.'),
('ten mask-only cells','composition_parts_loop0','Same macro-selected ten positions at point0 and C1-columns+column; ascending initialization, each selected_claim and array restoration retained. Generic loop models this exact macro schedule, whose helper source association remains a named row.'),
('boxed_at_point then poseidon_selectors, projected poseidon, semantic_packed','composition_source554 middle','Complete selector constructor, then terminal57 prefix; projected Poseidon consumes the same openings and selected fields. Semantic call follows it with the same original public Option and full selectors. Distinct statement49 constructor is never selected here.'),
('h1 read and copy_variant then evaluate_with_selectors','composition_source554 copy stage','SELECTED_H1_COLUMN constant read and claim0 field before variant conversion; same lambda,chi,next_pair_index and selectors arguments; all copy return fields retained. No oracle or callback is replaced by a model value.'),
('prepare theta and reverse semantic then poseidon loops','horner_direct_loop8 semantic and poseidon','Same prepared multiplier, copy.residual initial accumulator, semantic length24 decreasing index before read, then poseidon length4 using returned accumulator. Each step prepared.mul(composition).add(values[index]) keeps field operation order. Named body and loop binding8 laws preserve fail/divergence and every index; no Horner reassociation.'),
('Ok tuple plus selected G claim','composition_source554 suffix','After both loops, SELECTED_G_COLUMN and selected_claim0 read, then tuple(final,z,mask_only,g,h1,copy.active). Every component and both Result layers preserved. No final-result-only projection.')])
rows=[]
for name,(model,theorem,steps) in maps.items():
 item=items[name];assert tokens(item['body'])==historical_body(original[name]['tokens']),name
 active=selected(tokens(item['body']))
 assert not any(n in active for n in ['path_lanes_factored','absorption_lanes_factored','add_preweighted_shared_selector'])
 if name=='add_path_lanes':assert 'path_lanes_literal'in active
 if name=='semantic_initial_and_absorption':assert 'absorption_lanes_literal'in active
 if name=='add_value_lanes':assert 'residual'in active
 rows.append(dict(function=name,source=item,all_frozen_body_tokens_checked=True,active_tokens_sha256=hashlib.sha256('\0'.join(active).encode()).hexdigest(),active_tokens=active,interpreter=model,theorem='PV_B3P_Association554227.'+theorem,source_steps=[dict(source=s,model=m,argument=a)for s,m,a in steps]))
x=dict(functions=rows,source=dict(path=str(p),sha256=sha(p)),feature_graph=dict(reference='reference-projected/inputs.json',sha256=sha(R/'reference-projected/inputs.json'),selected=host['features'],fresh_recheck='DEPLOYED-FEATURE-RECHECK-D554.json',client_flags=['r1p-check','aspis-r1-cost-probe/ct-host-prover']),profile='release, debug_assertions=false, overflow_checks=false',correction='D550 handoff treated the distinct optimized dispatch as required; the specified deployed-client graph does not select it. No feature enabled or body edited.',route='Lean equality + own-1 structural, at the mechanically selected deployed source',domain='entire existing raw carrier; no new hypotheses',retained='named helper source obligations; full std/D188/native differential/matrix/callback and V370/D381/D386',status='pending focused compiles; no credit yet')
(R/'TERMINAL-SOURCE-D554.json').write_text(json.dumps(x,indent=2)+'\n');print('five whole frozen terminal bodies and active cfg branches checked')
