#!/usr/bin/env python3
"""Fail-closed structural validator for R433's native rows and current constructor source block."""
import hashlib,json,re
from pathlib import Path
ROOT=Path.cwd(); HERE=ROOT/'.r21-scratch/r433-actual-constructor-fragment/inventory'
LLBC=ROOT/'.r21-scratch/r431-actual-slice-construction/root-launch-a/saved-output/R431ActualSliceConstruction.llbc'
TABLE=HERE/'constructor86-command-table.json'
MODEL=ROOT/'.r21-scratch/r433-actual-constructor-fragment/R433ConstructorFragment.UNVERIFIED.lean'
EXPECTED_MODEL_SHA='816ea0b20355bcd23d06b0831841db279a08caa78cc59819abfebbb1fc04e2ef'
EXPECTED_LLBC_SHA='df9180ee7c9959a7840d6edac0b756f007ef33ed0bd88bb36faf57a3e18f2358'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def expect(ok,msg):
    if not ok:raise AssertionError(msg)

def extract_lists(block):
    found=[]; needle='sequence ['; start=0
    while True:
        i=block.find(needle,start)
        if i<0:break
        j=i+len('sequence '); assert block[j]=='['
        depth=0; end=None
        for k in range(j,len(block)):
            if block[k]=='[':depth+=1
            elif block[k]==']':
                depth-=1
                if depth==0:end=k;break
        expect(end is not None,'unterminated source sequence list')
        found.append(block[j+1:end]);start=end+1
    return found

def parse_command(s):
    s=' '.join(s.split())
    pats=[('live',r'\.live\s+(\d+)'),('dead',r'\.dead\s+(\d+)'),('metadata',r'\.metadata\s+(\d+)\s+(\d+)'),
      ('rawSlice',r'\.rawSlice\s+(\d+)\s+(\d+)\s+(\d+)'),('cast',r'\.cast\s+(\d+)\s+(\d+)\s+\.([A-Za-z0-9_]+)'),
      ('offset',r'\.offset\s+(\d+)\s+(\d+)\s+(\d+)'),('marker',r'\.marker\s+(\d+)'),
      ('iterator',r'\.iterator\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)'),('ret',r'\.ret')]
    for tag,pat in pats:
        m=re.fullmatch(pat,s)
        if m:return (tag,*[int(x) if x.isdigit() else x for x in m.groups()])
    raise AssertionError(f'unrecognized model command token: {s!r}')
def parse_seq(content):return [parse_command(s) for s in content.split(',') if s.strip()]
def strip_resolved(x):
    while isinstance(x,dict) and 'value' in x and ('ResolvedDeduplicated' in x or 'ResolvedHashConsedValue' in x):
        x=x['value']
    return x
def type_sig(t):
    t=strip_resolved(t)
    if isinstance(t,dict) and 'Literal' in t:
        v=t['Literal']
        if isinstance(v,dict) and v.get('UInt')=='Usize':return 'usize'
        return 'Literal('+json.dumps(v,sort_keys=True)+')'
    if isinstance(t,dict) and 'RawPtr' in t:
        elem,mut=t['RawPtr'];return f'*{mut} {type_sig(elem)}'
    if isinstance(t,dict) and 'Slice' in t:return f'[{type_sig(t["Slice"])}]'
    if isinstance(t,dict) and 'Adt' in t:
        a=t['Adt']; aid=(a.get('id') or {}).get('Adt')
        if aid==2:return 'QM31'
        if aid==58:return 'NonNull<QM31>'
        if aid==69:return 'NonNull<[QM31]>'
        if aid==42:return 'Iter<QM31>'
        if aid==59:return 'PhantomData<marker>'
        return f'Adt#{aid}'
    return json.dumps(t,sort_keys=True,separators=(',',':'))

def resolve(x,defs,stack=()):
    if isinstance(x,dict):
        if set(x)=={'Deduplicated'}:
            i=x['Deduplicated'];expect(i in defs,f'unresolved dedup type {i}');expect(i not in stack,f'dedup cycle at {i}')
            return resolve(defs[i],defs,stack+(i,))
        if set(x)=={'HashConsedValue'}:
            i,v=x['HashConsedValue'];expect(i not in stack,f'hashcons cycle at {i}')
            return resolve(v,defs,stack+(i,))
        return {k:resolve(v,defs,stack) for k,v in x.items()}
    if isinstance(x,list):return [resolve(v,defs,stack) for v in x]
    return x

def get_local_ref(rvalue,index):
    found=[o for o in rvalue['operand_references'] if o['mode'] in ('Copy','Move') and ((o.get('kind')=='Local' and o.get('index')==index) or o.get('root_operand')=={'id':index,'kind':'Local'})]
    expect(len(found)==1,f'expected one operand rooted in local {index}; got {len(found)}')
    return found[0]

def assignment(stmt,dst,opcode):
    expect(stmt['opcode']=='Assign' and stmt['destination']['local_alias']==dst,f'expected Assign to local {dst}: {stmt["path"]}')
    expect(stmt['rvalue']['opcode']==opcode,f'expected rvalue {opcode} at {stmt["path"]}')
    return stmt

llbc=load(LLBC); table=load(TABLE); model_text=MODEL.read_text()
expect(sha(LLBC)==EXPECTED_LLBC_SHA,'R431 input hash mismatch')
expect(table['input_sha256']==EXPECTED_LLBC_SHA,'table was built from a different R431 input')
expect(sha(MODEL)==EXPECTED_MODEL_SHA,'lead model source changed from the reviewed structural snapshot')
expect(llbc.get('has_errors') is False,'R431 LLBC has errors')
expect(table['function_id']==86 and table['top_level_statement_count']==28,'wrong function/count in command table')
# Parse and compare exact command-array structure from the source block.
start=model_text.index('def constructor86 : Program :=')
end=model_text.index('\ndef initial ',start)
block=model_text[start:end]
seqs=extract_lists(block)
expect(len(seqs)==4,f'expected prefix, true arm, false arm, tail lists; got {len(seqs)}')
prefix,yes,no,tail=map(parse_seq,seqs)
expected_prefix=[('live',0),('live',5),('live',2),('metadata',2,1),('live',3),('live',4),('live',8),('rawSlice',8,1,1),('cast',4,8,'sharedFatToNonNullFat'),('dead',8),('live',9),('live',10),('cast',10,4,'nonNullFatToMutFat'),('cast',9,10,'mutFatToMutThin'),('dead',10),('cast',3,9,'mutThinToNonNullThin'),('dead',9),('dead',4)]
expected_yes=[('cast',5,2,'wordToSharedThin')]
expected_no=[('live',6),('live',7),('cast',7,3,'nonNullThinToMutThin'),('offset',6,7,2),('dead',7),('cast',5,6,'mutThinToSharedThin'),('dead',6)]
expected_tail=[('live',11),('marker',11),('iterator',0,3,5,11),('dead',3),('dead',2),('dead',5),('dead',1),('dead',11),('ret',)]
expect(prefix==expected_prefix,'actual source prefix commands differ from reviewed expected sequence')
expect(yes==expected_yes and no==expected_no,'actual globalIf arm command sequence differs')
expect(tail==expected_tail,'actual post-branch command sequence differs')
expect('.globalIf 31' in block,'missing globalIf 31 in source block')
# Every top-level native statement gets an exact source-model position and all local storage ops are preserved.
ss=table['statement_commands'];expect(len(ss)==28,'native command table does not have 28 statements')
expect([s['opcode'] for s in ss]==['StorageLive','StorageLive','StorageLive','Assign','StorageLive','StorageLive','StorageLive','Assign','Assign','StorageDead','StorageLive','StorageLive','Assign','Assign','StorageDead','Assign','StorageDead','StorageDead','Switch','StorageLive','Assign','Assign','StorageDead','StorageDead','StorageDead','StorageDead','StorageDead','Return'],'native statement opcode sequence changed')
expect([ss[i]['local'] for i in [0,1,2,4,5,6,10,11,19]]==[0,5,2,3,4,8,9,10,11],'StorageLive indices differ')
expect([ss[i]['local'] for i in [9,14,16,17,22,23,24,25,26]]==[8,10,9,4,3,2,5,1,11],'StorageDead indices differ')
expect(ss[27]['opcode']=='Return','actual constructor return missing')
# Resolve canonical types and validate exact native cast source/destination type tuple for each modeled cast.
def row_type_decl(i):return llbc['translated']['type_decls'][i]['item_meta']['name']
def name_text(n):return '::'.join((x.get('Ident',[str(x)])[0] if isinstance(x,dict) else str(x)) for x in n if not (isinstance(x,dict) and ('Instantiated' in x or 'Impl' in x)))
type_names={i:name_text(row_type_decl(i)) for i in (2,42,58,59,69)}
expect(type_names=={2:'aspis_core::field::QM31',42:'core::slice::iter::Iter',58:'core::ptr::non_null::NonNull',59:'core::marker::PhantomData',69:'core::ptr::non_null::NonNull'},f'type declaration names changed: {type_names}')
source=load(LLBC)['translated']; defs={}
def collect(x):
 if isinstance(x,dict):
  h=x.get('HashConsedValue')
  if isinstance(h,list) and len(h)==2:defs.setdefault(h[0],h[1])
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(source)
cast_expect=[
 (ss[8],4,8,'sharedFatToNonNullFat','*Shared [QM31]','NonNull<[QM31]>'),
 (ss[12],10,4,'nonNullFatToMutFat','NonNull<[QM31]>','*Mut [QM31]'),
 (ss[13],9,10,'mutFatToMutThin','*Mut [QM31]','*Mut QM31'),
 (ss[15],3,9,'mutThinToNonNullThin','*Mut QM31','NonNull<QM31>'),
 (ss[18]['then_arm']['statements'][0],5,2,'wordToSharedThin','usize','*Shared QM31'),
 (ss[18]['else_arm']['statements'][2],7,3,'nonNullThinToMutThin','NonNull<QM31>','*Mut QM31'),
 (ss[18]['else_arm']['statements'][5],5,6,'mutThinToSharedThin','*Mut QM31','*Shared QM31')]
cast_report=[]
for s,dst,src,label,expected_src,expected_dst in cast_expect:
 expect(s['opcode']=='Assign' and s['destination']['local_alias']==dst,f'cast destination mismatch for {label}')
 rv=s['rvalue']['raw_rvalue'];expect('UnaryOp' in rv,f'cast rvalue is not UnaryOp for {label}')
 op=rv['UnaryOp'][0];expect(isinstance(op,dict) and 'Cast' in op,f'no explicit Cast node for {label}')
 castkind=next(iter(op['Cast']))
 expect(castkind in {'Transmute','RawPtr'},f'unknown cast opcode {castkind}')
 # The value-copy operand must identify the specified source local.
 operand=get_local_ref(s['rvalue'],src)
 actual_src=type_sig(operand['ty'])
 actual_dst=type_sig(s['destination']['resolved_place_type'])
 expect(actual_src==expected_src and actual_dst==expected_dst,
        f'type tuple mismatch {label}: {actual_src} -> {actual_dst}')
 # Independently require native cast operator endpoint types to agree with local source and destination types.
 endpoints=resolve(rv['UnaryOp'][0]['Cast'][castkind],defs)
 expect(isinstance(endpoints,list) and len(endpoints)==2,f'bad native cast endpoints at {s["path"]}')
 expect(type_sig(endpoints[0])==expected_src and type_sig(endpoints[1])==expected_dst,
        f'cast operator type endpoints mismatch for {label}: {type_sig(endpoints[0])} -> {type_sig(endpoints[1])}')
 cast_report.append({'model_cast':label,'native_path':s['path'],'dst_local':dst,'src_local':src,'native_cast_opcode':castkind,'source_type':actual_src,'target_type':actual_dst,'native_cast_endpoints':[type_sig(endpoints[0]),type_sig(endpoints[1])]})
# Metadata read and raw fat-pointer construction must retain the exact projected fields.
meta=ss[3]; expect(meta['destination']['local_alias']==2 and meta['rvalue']['opcode']=='Use','metadata assignment changed')
mr=meta['rvalue']['raw_rvalue']['Use'][0]['Copy']; expect(mr['kind']['Projection'][1]=='PtrMetadata' and mr['kind']['Projection'][0]['kind']['Local']==1,'metadata source is not CopyLocal1.PtrMetadata')
expect(type_sig(resolve(mr['ty'],defs))=='usize' and type_sig(meta['destination']['resolved_place_type'])=='usize','metadata type is not usize')
rawslice=ss[7]; expect(rawslice['destination']['local_alias']==8 and rawslice['rvalue']['opcode']=='RawPtr','raw fat pointer assignment changed')
rr=rawslice['rvalue']['raw_rvalue']['RawPtr']; expect(rr['kind']=='Shared','raw fat pointer mutability changed')
expect(rr['place']['kind']['Projection'][0]['kind']['Local']==1 and rr['place']['kind']['Projection'][1]=='Deref','raw pointer base is not Deref(Local1)')
pm=rr['ptr_metadata']['Copy'];expect(pm['kind']['Projection'][0]['kind']['Local']==1 and pm['kind']['Projection'][1]=='PtrMetadata','raw pointer metadata is not Copy(Local1.PtrMetadata)')
# Constructor branch and aggregate tuple shape remain exact.
sw=ss[18]; expect(sw['opcode']=='Switch' and sw['condition_operand_references'][0]['kind']=='Global' and sw['condition_operand_references'][0]['id']==31,'constructor branch is not Global31')
expect(type_sig(sw['condition_operand_references'][0]['ty'])=='Literal(\"Bool\")','Global31 branch condition type changed')
expected_offsets=(('else_arm',3,6,7,2),)
off=sw['else_arm']['statements'][3];expect(off['opcode']=='Assign' and off['destination']['local_alias']==6,'offset destination changed')
br=off['rvalue']['raw_rvalue']['BinaryOp'];expect(br[0]=='Offset','offset expression opcode changed')
expect(br[1]['Copy']['kind']['Local']==7 and br[2]['Copy']['kind']['Local']==2,'offset operands are not CopyLocal7, CopyLocal2')
offrefs=off['rvalue']['operand_references'];expect([(o['mode'],o.get('index')) for o in offrefs]==[('Copy',7),('Copy',2)],'offset operands are not exactly Copy7, Copy2')
expect([type_sig(o['ty']) for o in offrefs]==['*Mut QM31','usize'],'offset operand types changed')
expect(type_sig(off['destination']['resolved_place_type'])=='*Mut QM31','offset result type changed')
mark=ss[20];expect(mark['destination']['local_alias']==11 and mark['rvalue']['opcode']=='Aggregate','marker assignment changed')
ma=mark['rvalue']['raw_rvalue']['Aggregate'];expect(ma[0]['Adt'][0]['id']=={'Adt':59} and ma[1]==[],'marker is not zero-operand ADT type 59')
iter_stmt=ss[21];expect(iter_stmt['destination']['local_alias']==0 and iter_stmt['rvalue']['opcode']=='Aggregate','Iter construction aggregate changed')
ia=iter_stmt['rvalue']['raw_rvalue']['Aggregate'];expect(ia[0]['Adt'][0]['id']=={'Adt':42},'iterator aggregate is not type 42')
expect(len(ia[1])==3 and [next(iter(x)) for x in ia[1]]==['Copy','Copy','Move'],'iterator fields are not Copy,Copy,Move')
expect([ia[1][0]['Copy']['kind']['Local'],ia[1][1]['Copy']['kind']['Local'],ia[1][2]['Move']['kind']['Local']]==[3,5,11],'iterator operands differ')
expect([type_sig(resolve(ia[1][0]['Copy']['ty'],defs)),type_sig(resolve(ia[1][1]['Copy']['ty'],defs)),type_sig(resolve(ia[1][2]['Move']['ty'],defs))]==['NonNull<QM31>','*Shared QM31','PhantomData<marker>'],'iterator operand types changed')
report={
 'status':'passed','model_path':str(MODEL.relative_to(ROOT)),'model_sha256':sha(MODEL),
 'constructor_llbc_path':str(LLBC.relative_to(ROOT)),'constructor_llbc_sha256':sha(LLBC),'command_table_sha256':sha(TABLE),
 'source_block_sha256_gate':EXPECTED_MODEL_SHA,'parsed_sequence_command_counts':[len(prefix),len(yes),len(no),len(tail)],
 'statement_shape_checks':{'top_level_count':28,'all_top_level_statement_opcodes_and_local_indices_match':True,'prefix_18_then_1_else_7_tail_9_match':True,'all_storage_operations_and_return_match':True},
 'metadata_and_pointer_shape_checks':{'metadata_copy_local1_ptrmetadata_to_local2_usize':True,'raw_shared_slice_pointer_local1_metadata_local1_to_local8':True,'global31_branch':True,'offset_local7_plus_local2_to_local6':True},
 'cast_tuples':cast_report,
 'aggregate_checks':{'marker_local11_zero_operand_type59':True,'iter_local0_type42_fields_copy_local3_copy_local5_move_local11':True},
 'boundary':'This validates only exact AST command ordering/opcodes/operands and type-node structure against this frozen draft. It does not establish the modeled cast ABI, pointer provenance/lifetimes, allocation/heap representation, source execution equivalence, or Rust unsafe-precondition satisfaction; no Lean run was performed.'}
(HERE/'model-binding-verification.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print('verified source-block prefix/branches/tail',report['parsed_sequence_command_counts'],'casts',len(cast_report))
