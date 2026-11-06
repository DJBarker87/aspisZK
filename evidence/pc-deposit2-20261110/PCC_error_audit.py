"""Read-only frozen-source error-consumer inventory; no semantic proof credit."""
from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent
rows=json.loads((E.parent/'pool-inventory2-20261109/NKZ_INVENTORY.json').read_text())['rows']
ids=[328,309,313,199,304,222,220,326,301,362,340,332,367,365,388,382,364,358,333,395,286,356,357]
snapshots={};sites=[];functions=[]
for number in ids:
 r=next(r for r in rows if r['id']==f'POOL:{number}')
 file=r['source_file'];revision='b936275465600469312d1f058cdc91ea2a11f3dc' if file.startswith('programs/aspis-pool/') else '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 raw=subprocess.check_output(['git','show',revision+':'+file]);sha=hashlib.sha256(raw).hexdigest()
 snapshots[sha]=dict(path=file,revision=revision,sha256=sha)
 start,end=r['source_lines'];lines=raw.decode().splitlines();functions.append(dict(row=r['id'],function=r['function'],source_sha256=sha,range=[start,end]))
 for ln in range(start,end+1):
  text=lines[ln-1]
  if not any(k in text for k in ['?','map_err','Err(','is_err','match ','and_then']):continue
  kind='SOURCE_REVIEW_REQUIRED'
  if 'map_err(|_|' in text:kind='CONSTANT_ERROR_MAP_NO_PAYLOAD_INSPECTION'
  elif '?' in text:kind='QUESTION_MARK_PROPAGATION_OR_MAP_TERMINATOR'
  elif 'Err(' in text:kind='ERROR_CONSTRUCTION'
  elif 'and_then' in text:kind='RESULT_TAG_DISPATCH'
  sites.append(dict(row=r['id'],file=file,line=ln,text=text.strip(),classification=kind,full_value_retained=True))
# Post-row path: the selected AS8D dispatcher and the native runtime forwarding.
for start,end,label in [(491,628,'dispatcher'),(204,266,'nested create_or_allocate_pda_with_rent')]:
 file='programs/aspis-pool/src/processor.rs';raw=subprocess.check_output(['git','show','b936275465:'+file]);lines=raw.decode().splitlines()
 for ln in range(start,end+1):
  text=lines[ln-1]
  if '?' in text or 'is_err' in text or 'Err(' in text:
   sites.append(dict(row=label,file=file,line=ln,text=text.strip(),classification='TAG_ONLY_FULL_RESULT_RETAINED' if 'is_err' in text else 'PROPAGATION_OR_ERROR_CONSTRUCTION',full_value_retained=True,off_selected_branch_possible=label=='dispatcher'))
result=dict(status='PARTIAL_INVENTORY_NOT_E1_CLOSURE',functions=functions,source_pins=list(snapshots.values()),sites=sites,
 entrypoint=dict(package='solana-program-entrypoint 2.3.0',macro_lines=[128,140],error_arm='Err(error) => error.into()',payload_observed=False),
 limits=['Direct children plus nested rent helper and dispatcher only; transitive child error consumers must be audited with their functional packet.', 'Cfg arms are retained text; selected deployed arms require per-site review.', 'No native association or complete error transport claimed.'])
(E/'PCC_ERROR_PROPAGATION.json').write_text(json.dumps(result,indent=1)+'\n')
print('Frozen direct-child error inventory recorded; transitive review remains OPEN')
