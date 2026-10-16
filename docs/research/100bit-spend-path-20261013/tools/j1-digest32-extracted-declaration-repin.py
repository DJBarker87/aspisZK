#!/usr/bin/env python3
"""Read/hash audit of all LLBC declarations in the accepted R1 extraction cones.

No Rust/Lean execution. Historical unsuccessful/superseded translations are not
promoted to current source. Include types, functions, globals, traits and impls,
including closures/derived definitions; axiom freedom is a separate property.
"""
from pathlib import Path
import argparse,collections,difflib,hashlib,json,subprocess,tarfile
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
CURRENT='c16ab4d76619cf2cf80ece9d7e60e47975957af0'
BEFORE='ca137f5db'
MIGRATED='b92ab28465f9ffd4edcd3e2d5300cc9306ba66af'
CONES=[
 ('decoder','terminal-decoder-copy-helper-20261016/translation.tar.gz','copy-helper/extraction-a/TerminalDecoder.llbc',None),
 ('validator','terminal-validator-extraction-20261016/evidence.tar.gz','final/extraction/TerminalValidator.llbc',None),
 ('adapter','adapter-reconstruct-432-20261016/source-extraction-proofs.tar.gz','extraction-a/AdapterReconstruct.llbc','adapter-reconstruct-extraction-kit/source-pins.json'),
 ('preparation','public-preparation-step-20261016/public-preparation-extraction.tar.gz','PublicPreparation.llbc','public-preparation-extraction-kit/source-pins.json'),
 ('metadata','readonly-meta-20261016/readonly-meta-evidence.tar.gz','extraction/ReadonlyMeta.llbc','readonly-meta-extraction-kit/source-pins.json'),
]
sha=lambda b:hashlib.sha256(b).hexdigest()
def blob(rev,path):return subprocess.check_output(['git','-C',str(ROOT),'show',rev+':'+path],stderr=subprocess.DEVNULL)
def positions(raw):
 lines=raw.splitlines(keepends=True);out=[0]
 for line in lines:out.append(out[-1]+len(line))
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
 changed=subprocess.check_output(['git','-C',str(ROOT),'diff','--name-only',BEFORE,MIGRATED,'--','*.rs'],text=True).splitlines()
 actual={path:blob(CURRENT,path) for path in changed};records=[];inputs=[];unresolved=[]
 for label,archive,member,kit in CONES:
  path=BASE/'evidence'/archive
  with tarfile.open(path) as tar:raw=tar.extractfile(member).read()
  d=json.loads(raw)['translated'];pins=json.loads((BASE/'tools'/kit).read_text()) if kit else None
  inputs.append(dict(cone=label,archive=str(path.relative_to(ROOT)),archive_sha256=sha(path.read_bytes()),llbc_member=member,llbc_sha256=sha(raw),kit=kit))
  for kind in ['type_decls','fun_decls','global_decls','trait_decls','trait_impls']:
   for x in d[kind]:
    if not x:continue
    m=x['item_meta'];span=m['span']['data'];f=d['files'][span['file_id']];name=f['name'];source=name.get('Local',name.get('Virtual',''))
    text=m.get('source_text');targets=[]
    if text is None and f.get('contents') is not None:
     lines=f['contents'].splitlines(keepends=True);beg,end=span['beg'],span['end'];joined=''.join(lines[beg['line']-1:end['line']]);text=joined[beg['col']:len(joined)-len(lines[end['line']-1])+end['col']]
    if text is None and source in actual:
     # Dependency metadata can omit source contents. Recover its exact span
     # only from the manifest's historical Git revision, never current bytes.
     rev=(pins or {}).get('source_revision')
     assert rev,(label,kind,m['name'])
     lines=blob(rev,source).decode().splitlines(keepends=True);beg,end=span['beg'],span['end'];joined=''.join(lines[beg['line']-1:end['line']]);text=joined[beg['col']:len(joined)-len(lines[end['line']-1])+end['col']]
    if source in actual:targets=[source]
    elif source=='lib.rs' and text and pins:
     # Namespace-only cuts retain each entire declaration. For each current
     # changed source, test the exact emitted source text, not tokens.
     candidates=pins.get('source_files',{}).keys()
     if pins.get('layout_spans'):
      content=f['contents'].encode();offs=positions(content);at=offs[span['beg']['line']-1]+span['beg']['col']
      containing=[q for q in pins['layout_spans'] if q.get('start_byte',q.get('byte_start',-1))<=at<q.get('end_byte_exclusive',q.get('byte_end_exclusive',-1))]
      if not containing:
       assert m['name'][-1].get('Ident',[''])[0]=='sample_validated_entry',(label,kind,m['name'],at)
       continue
      assert len(containing)==1,(label,kind,m['name'],at)
      cut=next(q for q in pins['cuts'] if q['name']==containing[0]['name']);candidates=[cut['path']]
     if pins.get('source_path'):candidates=[pins['source_path']]
     if isinstance(pins.get('sources'),list):candidates=[q['source'] for q in pins['sources']]
     targets=[q for q in candidates if q in actual]
    if not targets:continue
    assert text is not None,(label,kind,m['name'])
    for target in targets:
     if text.encode() not in actual[target]:
      unresolved.append(dict(cone=label,kind=kind,name=m['name'],source_path=target,historical_source_text_sha256=sha(text.encode()),reason='Historical emitted declaration source differs; not silently omitted or relabelled. New extraction/statement diff required.'));continue
     start=actual[target].index(text.encode());rec=dict(cone=label,kind=kind,id=x.get('def_id'),name=m['name'],source_path=target,classification='unchanged',source_text_sha256=sha(text.encode()),current_start_byte=start,current_end_byte_exclusive=start+len(text.encode()),current_file_sha256=sha(actual[target]),historical_llbc_source_file=source,historical_span=span,statement_diff='',notes='Exact source text retained, including any derived/closure source span. No axiom-freedom or runtime claim.')
     records.append(rec)
 # Prefix source cuts cover the accepted parser aggregate emission. Their
 # original LLBC is not retained locally; exact kit/Lean mirrors stay pinned.
 pinpath=BASE/'tools/prefix-aggregate-extraction-kit/source-pins.json';pins=json.loads(pinpath.read_text())
 for q in pins['declaration_cuts']:
  target=q['path']
  if target not in actual:continue
  lines=actual[target].splitlines(keepends=True);text=b''.join(lines[q['first_line']-1:q['last_line']])
  # Migration adds only code after these cuts; byte hashes are the source key.
  if sha(text)!=q['sha256']:text=text.rstrip(b'\n')
  assert sha(text)==q['sha256'],q['name']
  records.append(dict(cone='prefix-aggregate',kind='exact_declaration_cut',name=q['name'],source_path=target,classification='unchanged',source_text_sha256=sha(text),current_file_sha256=sha(actual[target]),current_lines=[q['first_line'],q['last_line']],statement_diff=''))
 # The old SDK wrapper was deliberately superseded by helper/projection.
 old=json.loads((BASE/'tools/readonly-account-extraction-kit/source-pins.json').read_text());target=old['source'];before=old['exact_declaration'];after=(BASE/'tools/readonly-meta-extraction-kit/source-pins.json');after=json.loads(after.read_text())['sources'][0]['declarations']['require_readonly_account']['declaration']
 assert after.encode() in actual[target] and before.encode() not in actual[target]
 records.append(dict(cone='readonly-account-superseded',kind='function',name='require_readonly_account',source_path=target,classification='re-extracted',historical_source_text_sha256=sha(before.encode()),source_text_sha256=sha(after.encode()),statement_diff=''.join(difflib.unified_diff(before.splitlines(keepends=True),after.splitlines(keepends=True),fromfile='old SDK wrapper extraction',tofile='current projection wrapper')),proof_statement_diff='Old actual AccountInfo wrapper result is no longer the current extracted function. Current extracted readonly_meta_ok proves exact Result over owner/flags; R16ReadonlyMetadataProjection connects actual wrapper to that one helper premise. Custody is separate.',replacement_evidence='evidence/readonly-meta-20261016/readonly-meta-evidence.tar.gz',current_file_sha256=sha(actual[target])))
 coverage=collections.Counter(q['source_path'] for q in records)
 result=dict(source_revision=CURRENT,migration_before=BEFORE,migration_tip=MIGRATED,inputs=inputs,scope='All type/function/global/trait/impl LLBC entries in the enumerated accepted R1 cones, plus all accepted Prefix declaration cuts. Superseded SDK wrapper recorded explicitly. No claim about historical failed experiments or unrelated V8 cones. Current generated caller cone added separately once emission succeeds.',declarations=records,file_coverage=[dict(source_path=q,source_sha256=sha(actual[q]),inventory_entries=coverage[q],note='No extracted declaration in enumerated accepted R1 cones' if not coverage[q] else '') for q in changed],counts=dict(collections.Counter(q['classification'] for q in records)),unresolved_declarations=unresolved,inventory_gate='OPEN: enumerated accepted-cone subset; full migration universe and superseded-wrapper boundary must be reconciled',outstanding=['Supported caller52 emission and its statement diff are separate.','Actual begin/verify/opening full33 refinement and source provenance remain unproved; this hash inventory cannot supply them.'])
 dest=BASE/'design/J1-DIGEST32-EXTRACTED-DECLARATION-REPIN-20261016.json';raw=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
 if args.check:assert dest.read_bytes()==raw
 else:dest.write_bytes(raw)
 print(json.dumps(dict(status='PASS',counts=result['counts'],changed_files=len(changed),covered_files=len(coverage),inventory_sha256=sha(raw))))
if __name__=='__main__':main()
