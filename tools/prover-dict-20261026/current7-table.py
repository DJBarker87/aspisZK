"""Current source requirements; never turn reference paths into execution witnesses."""
from pathlib import Path
import json,shutil
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026'
snapshot=e/'pure7/installed-before.json'
if not snapshot.exists():shutil.copyfile(e/'installed-and-remaining.json',snapshot)
x=json.loads(snapshot.read_text());reach=json.loads((e/'reach7/reachability.json').read_text())
new={i:'R1Z.PDict_PureDictionary.op'+str(i)+'_installed' for i in [37,40,41,43,44,60,235,236,239,240,260]}
new.update({i:'R1Z.PDict_CodecDictionary.op'+str(i)+'_installed' for i in [49,50]})
absent={13,16,17,18,85,124,238};before={z['id'] for z in x['functions'] if z['status']!='OPEN'}
assert not before&new.keys();assert len(before)==163
for z in x['functions']:
 i=z['id'];z['required_by_source_bound']=i not in absent
 if i in new:z.update(status='new source interpretation',theorem=new[i],native_qualification='Exact current standalone Charon/baseline Aeneas extraction; complete body only, no external template; see pure7/source-cuts.json and codec/source-cut.json. Whole native caller/effect and release-artifact adequacy remain open.')
 if i in absent:z['irrelevance_theorem']=f'R1Z.PDict_ReachCaller.op{i}_irrelevant'
sel={z['id'] for z in x['functions'] if z['status']!='OPEN'};required=set(range(262))-absent
x.update(selector='R1Z.PDict_CodecDictionary.selected',types='R1Z.PDict_CodecDictionary.native',new_source_entries=114,source_selected_total=len(sel),remaining_function_count=262-len(sel),required_source_denominator=len(required),required_source_selected=len(sel&required),required_remaining_function_count=len(required-sel),removed_source_fields=sorted(absent),root_premises_removed=0)
assert (x['source_selected_total'],x['required_source_selected'],x['required_remaining_function_count'])==(176,172,83)
for t in x['type_entries']:
 if t['id']==3:t['reference_progress']='PDict_OwnedErrorSource and PDict_OwnedErrorCorrect: non-dynamic reference extracted and proved;15 scoped Kani runs,12 pass. Universal reachable-native quotient, ownership/world and full caller composition remain open; not a native type binding.'
 if t['id']==27:t['reference_progress']='Seven source callbacks erased; PDict_FormatterDictionaryMap retypes all262 fields with structural carrier/trait maps; store/path transport checked. Whole caller transport and native carrier/effects remain open.'
x['qualification']='172 selected /83 open /255 is a sufficient extracted-source requirement. It is not an exact positive native invocation count.176/262 is the historical full-dictionary selection view. Native types26/28; no root RunJoin/headline premise removed.'
(e/'installed-and-remaining.json').write_text(json.dumps(x,indent=2)+'\n')
lines=['# Installed prover dictionary and current source requirement','','Target not yet established. **172 selected /83 open /255 sufficient required source fields**. Historical full dictionary:176 selected /86 open /262. Seven field irrelevances remove four selected and three open fields. Positive feasible-native-invocation counts remain unestablished. Native type-value associations:26/28;3 IOError and27 Formatter remain open. Root premises removed:0.','','| ID | Name | Required by source bound | Selection / theorem |','|---:|---|---|---|']
for z in x['functions']:
 note=z['status']+'; `'+(z.get('theorem') or 'inherited selection' if z['status']!='OPEN' else 'OPEN')+'`'
 if z['id'] in absent:note+='; `'+z['irrelevance_theorem']+'`'
 lines.append(f"|{z['id']}|`{z['name']}`|{'yes' if z['required_by_source_bound'] else 'no'}|{note}|")
lines+=['','## Types','','| ID | Name | Status / evidence |','|---:|---|---|']
for z in x['type_entries']:lines.append(f"|{z['id']}|`{z['name']}`|{z['status']}; `{z.get('theorem') or 'open'}`; {z.get('reference_progress',z['support'])}|")
lines+=['','File value representation does not supply OS authority or world transport. New File ABI checks retain their stated finite schedules; arbitrary retries, open/create_new/mode, dynamic payload/vtables, side channels, native-world/Drop composition and whole RunJoin remain open. Serializer op51 retains its callback because iterator/chunk templates are unselected. No simulator, observer, bad event, seed, adversary, witness, protocol, shipped source, artifact pin or root theorem changed.']
(e/'ENTRIES.md').write_text('\n'.join(lines)+'\n')
oldopen={z['id'] for z in json.loads(snapshot.read_text())['functions'] if z['status']=='OPEN'}
for z in reach['operations']:
 i=z['id']
 if i in new:z['current_source_entry']=new[i]
 z['required_now']=i not in absent
reach['proved_source_requirements']=dict(selected=172,open=83,denominator=255,removed=sorted(absent),qualification='Sufficient source dependency bound; positive native execution remains unproved')
reach['type_progress']={str(z['id']):z.get('reference_progress') for z in x['type_entries'] if z['id'] in [3,27]}
for t in reach['types']:t['status']=reach['type_progress'][str(t['id'])]
(e/'reach7/reachability.json').write_text(json.dumps(reach,indent=2)+'\n')
l=['# Caller reachability and current source requirement','','Target not yet established. 163/99/262 becomes159/96/255 after the proved seven-field source erasure, then172/83/255 after13 exact pure entries. This is a sufficient extracted-source bound, not an exact native invocation denominator. All99 original open-operation rows are retained below. Native invocation traces/effects and positive feasible execution remain open.','','| Op | Name | Current source requirement | Evidence |','|---:|---|---|---|']
for z in reach['operations']:
 i=z['id']
 if i not in oldopen:continue
 note='absent / not required' if i in absent else 'retained; selected source body' if i in new else 'retained; open'
 evidence=f'R1Z.PDict_ReachCaller.op{i}_irrelevant' if i in absent else new.get(i,'reference path only in reachability.json; feasible execution unresolved')
 l.append(f"|{i}|`{z['name']}`|{note}|`{evidence}`|")
assert len(oldopen)==99
l+=['','## Types','','| ID | Type | Status |','|---:|---|---|','|3|std.io.error.Error|Native binding open; extracted owned reference and scoped native observations complete, full reachable/native/world quotient open|','|27|core.fmt.Formatter|Native binding open; full dictionary retyping plus store/path transport checked, whole caller carrier transport open|','','26/28 native lower type values remain selected. File ownership/world and root refinement/headline premises remain unchanged. No new premises;13 pure source-entry obligations and three irrelevant open source callbacks removed from the stated source requirement.']
(e/'reach7/REACHABILITY.md').write_text('\n'.join(l)+'\n')
print('172 /83 /255 required;176 /262 full;26 /28 types; root0')
