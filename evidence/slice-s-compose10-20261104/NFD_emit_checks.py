"""Emitter prefix and owned-return continuation, composed by identical result place."""
import subprocess
import NFD_validate as v
from NFD_native_checks import native
from NFD_composition_support import source,structural
from NFD_bridge_checks import REV
E=v.E
F='programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result'
THMS=['NEY_EmitComposed.result_state_effects','NEY_EmitComposed.reached_encoder','NEY_EmitComposed.encoder_bridge','NFD_EmitProjection.complete']+[f'NFD_EmitProjection.alignment{i}' for i in range(8)]
ATTEMPTS=[f'NFD_K{n:03}' for n in range(87,91)]+[f'NFD_K{n:03}' for n in range(111,127)]
EXTRAS=['NFD_EMIT_PREFIX_TEMPLATE.json','NFD_EMIT_CONTINUATION_TEMPLATE.json']
CLASS='actual statement getters and complete derived result on unrestricted typed statement; SAME result borrowed by binding/encoder; ordered full Result then exact single792-byte setReturnData event; conservative method targets retained and covered'
DOMAIN='all typed terminal statements; every raw field, binding/encoder error and full792-byte encoder reply; reached successful encoder domain derived from SAME binding success'
def prefix_source(slot,mode):
 t=v.read(E/'NFD_EMIT_PREFIX_TEMPLATE.json');assert v.sha(t['source'].encode())==t['source_sha256']=='39ad465b7ab4ea315a139801e8db91f0b792481825733ad63858a46d33a235d6'
 m=v.read(E/'NFD_K111-shape.json')
 return t['source'].replace('assert!(('+m['fields'][0]+')==('+m['values'][0]+'));','assert!(('+m['fields'][slot]+')==('+m['values'][slot]+')'+('^1' if mode=='negative' else '')+');')
def continuation_source(mode):
 t=v.read(E/'NFD_EMIT_CONTINUATION_TEMPLATE.json');assert v.sha(t['source'].encode())==t['source_sha256']=='3ee3b3c13dad26261d3ee09da573a81b8f42cfe7ac1769a6dfc7e656bc66d711'
 s=t['source']
 if mode=='byte':s=s.replace('Some(frame.byte)','Some(frame.byte^1)')
 if mode=='order':s=s.replace('frame.calls==3&&','frame.calls==2&&')
 if mode=='argument':s=s.replace('send(&encoded,f)','send(&encoded[1..],f)')
 return s
def check(c,base):
 assert c['subject']==F
 assert c['native_certificate']==dict(function=F,complete=True,domain=DOMAIN,pairs=[[f'NFD_K{111+2*i:03}',f'NFD_K{112+2*i:03}'] for i in range(8)],continuation=['NFD_K087','NFD_K088','NFD_K089','NFD_K090'])
 f=subprocess.check_output(['git','show',REV+':'+F.split('::')[0]],text=True);a=f.index('fn emit_result(');original=f[a:f.index('\n}',a)+2]
 for slot in range(8):
  for off,mode in enumerate(['positive','negative']):
   a=f'NFD_K{111+2*slot+off:03}';snap=native(a,mode=='positive');m=v.read(E/(a+'-shape.json'))
   assert m['slot']==slot and m['mode']==mode and m['frozen_body']==original
   assert source(snap['NFD_native_contracts.patch'],'NFD_emit_prefix')==prefix_source(slot,mode)
   expected=original[:original.index('    validate_pool_v1_pair_forest_terminal_result_against_statement_v1')].replace('fn emit_result(','fn native(').replace('-> ProgramResult','-> PoolV1PairForestTerminalResultV1')+'    result\n}\n'
   assert m['native']==expected and expected in prefix_source(slot,mode)
 for a,mode in zip(['NFD_K087','NFD_K088','NFD_K089','NFD_K090'],['positive','byte','order','argument']):
  snap=native(a,mode=='positive');m=v.read(E/(a+'-shape.json'))
  assert m['mode']==mode and m['frozen_body']==original
  assert source(snap['NFD_native_contracts.patch'],'NFD_emit_continuation')==continuation_source(mode)
 s=continuation_source('positive');m=v.read(E/'NFD_K087-shape.json')
 from NEY_bridge_checks import undo
 restored=m['native'].split('{\n',1)[1]
 for new,old in [('binding','validate_pool_v1_pair_forest_terminal_result_against_statement_v1'),('encode','encode_pool_v1_pair_forest_terminal_result_v1'),('send','program::set_return_data')]:restored=undo(restored,new,old)
 assert restored==original[original.index('    validate_pool_v1_pair_forest_terminal_result_against_statement_v1'):]
 assert all(x in s for x in ['f.calls==0&&core::ptr::eq(s,f.s)','core::ptr::eq(r,f.record)','let raw:[u8;792]=kani::any()','bytes.len()==792','f.sent=Some(bytes[f.j])','frame.sent==Some(frame.byte)','frame.calls==1&&frame.sent==None','frame.calls==2&&frame.sent==None'])
 assert s.count('send(&encoded,f)')==1
 assert 'RuntimeReturnData' in c['hypotheses'] and c['new_trust_rows']==['RuntimeReturnData']
 return structural(c,F,THMS,base,ATTEMPTS,EXTRAS,CLASS,['RuntimeReturnData'])
