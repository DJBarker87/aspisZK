from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-own-20261028'
rows=json.loads((E/'drop-mir.json').read_text());by={Path(x['path']).name:x for x in rows};checks=[]
for tag in ['PoolV1PairCopyRowLinkV1','u16','(usize,QM31)','u8']:
 p=by['core.ptr-drop_in_place.Vec_'+tag+'_.runtime-optimized.after.mir'];s=p['text']
 assert 'as Drop>::drop(move _2) -> [return: bb4, unwind: bb3]' in s
 for block in ['bb3 (cleanup):','bb4:']:
  body=s.split(block,1)[1].split('\n    }',1)[0];assert 'drop(' in body and 'RawVec<' in body
 checks.append(dict(type='Vec<'+tag+'>',source_mir_sha256=p['sha256'],normal=['Vec::drop (POD slice)','RawVec::drop'],unwind=['RawVec::drop','resume or terminate on double unwind']))
s=by['core.ptr-drop_in_place.String.runtime-optimized.after.mir']['text'];assert 'drop(((*_1).0: std::vec::Vec<u8>))' in s
s=by['core.ptr-drop_in_place.Box_PoolV1PairCopyRowLinkV1_.runtime-optimized.after.mir']['text'];assert 'drop((*_6)) -> [return: bb3, unwind: bb4]' in s
for block in ['bb3:','bb4 (cleanup):']:assert 'as Drop>::drop' in s.split(block,1)[1].split('\n    }',1)[0]
root=next(x for x in rows if '/deps/' in x['path']);assert 'Path::join::<String>(move _1, move _2)' in root['text']
j=dict(checks=checks,string_delegates='Vec<u8>',box_order=['pointee drop','Box::drop'],owned_join='String moved into Path::join<String>; wrapper contains no inline argument destructor',classification='deployed-configuration probe MIR shape check plus finite validation; NOT a native-to-byte-world theorem or structural K-1 substitute',composition_trust='Compiler/MIR agreement reclassification within existing tool trust',row_restored=False)
(E/'drop-mir-audit.json').write_text(json.dumps(j,indent=2)+'\n');print('MIR normal/unwind edges checked for four Vec instantiations, String and Box')
