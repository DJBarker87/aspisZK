"""Generate the Pool slot map from frozen PCM sources and merged supplier packets."""
from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
freeze=json.loads((E/'PCM_SPEC_FREEZE.json').read_text())
for row in freeze['sources']:assert hashlib.sha256((R/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
inv=json.loads((E.parent/'pool-inventory2-20261109/NKZ_INVENTORY.json').read_text())
byid={r['id']:r for r in inv['rows']}
base=json.loads(lzma.open(E.parent/'pool-ledger1-20261110/PCE_LEDGER.json.xz').read())
sup={r['id']:dict(row=r['id'],status=r['status'],root=r.get('root'),clauses=r.get('caller_clauses',[]),packet='PCE_LEDGER.json.xz') for r in base['rows']}
for folder,pre in [('pc-helpers2-20261110','PCG'),('pc-deposit-children1-20261110','PCF'),('pc-deposit-children2-20261110','PCI'),('pc-terminal-children1-20261110','PCD')]:
 p=E.parent/folder/(pre+'_CLOSED.json');j=json.loads(p.read_text());rs=j if isinstance(j,list) else j['rows']
 for r in rs:
  rid=r.get('id',r.get('row'));sup[rid]=dict(row=rid,status='CLOSED',root=r['root'],clauses=r.get('own_argument_domain',r.get('caller_clause',r.get('domain',[]))),packet=str(p.relative_to(R)))
# Actual source-level calls, not broad MIR name alternatives. SDK callbacks
# are indexed by their consuming OPEN row when no separate inventory row exists.
M={
328:{'decodeMaster':313,'noteCommitment':165,'depositLane':199,'decodeLane':304,'singleOutput':222,'leafDigest':220,'prepareAppend':326,'rootLocation':246,'zeroedPage':301,'pageAddress':280,'freshPda':362,'currentPage':340,'exactCount':332,'uniqueAccounts':367,'tokenProgram':365,'planTransfer':388,'transferInfos':382,'payerAndSystem':364,'createPda':358,'programOwnedZeroed':333,'exactDelta':395,'writeNewPage':286,'appendRoots':279},
330:{'decodeRequest':314,'decodeMaster':313,'decodeCheckpoint':311,'outputLane':200,'decodeLane':312,'requestAccounts':341,'spendLayout':322,'payerAndSystem':364,'planMarker':294,'tokenProgram':365,'planWithdrawal':389,'createMarker':361,'verify':347,'validateResult':339,'nextLaneImage':319,'resultBytes':337,'withdrawalInfos':383,'exactDelta':396,'writeNewPage':286,'appendRoots':279,'setReturnData':330},
327:{'exactCount':332,'uniqueAccounts':367,'payerAndSystem':364,'planCheckpoint':321,'freshPda':362,'decodeCheckpoint':190,'createPda':358,'programOwnedZeroed':333},
350:{'proofTransport':351,'requireProgram':353,'distinctCheckpoint':352,'authenticate':372,'matchesOwner':371,'matchesSelection':370},
348:{'requireProgram':353,'proofTransport':351,'distinctCheckpoint':352,'decodeResult':208},
347:{'plan':349,'invoke':348},
319:{'nextLane':320,'encodeLane':315},
339:{'validate':213},
326:{'append':181,'encode':191},
333:{'programAccount':285,'rentExempt':333},
358:{'rentGet':358,'withRent':359},
361:{'seedString':296,'createWithSeed':360,'recheck':298,'rentExempt':361},
340:{'programAccount':285,'addressWithBump':284,'address':283,'validatePage':247,'retainedRoot':248},
341:{'outputLane':200,'laneMatches':317},
322:{'zeroedPage':301,'address':284,'programAccount':285,'currentPage':340,'exactCount':332,'uniqueAccounts':367},
321:{'aliasFree':331,'master':302,'lanes':303,'globalRoot':324,'checkpointAddress':323,'purePlan':198,'freshPda':362,'encodeMaster':193,'encodeCheckpoint':192},
294:{'encode':185,'canonicalNullifier':177,'address':292,'classify':295},
349:{'encode':206,'plan':350},
}
# Validate spellings below against the NKZ table and correct any ambiguous
# guessed numeric id using the exact frozen symbol name; ambiguity is fatal.
expected={
(333,'programAccount'):'require_program_account',(340,'programAccount'):'require_program_account',(322,'programAccount'):'require_program_account',
(340,'addressWithBump'):'require_root_page_address_with_bump',(340,'address'):'require_root_page_address',
(340,'validatePage'):'validate_root_page_bytes',(340,'retainedRoot'):'read_retained_root',
(341,'laneMatches'):'lane_address_matches',(322,'address'):'require_root_page_address_with_bump',
(321,'aliasFree'):'require_alias_free',(321,'master'):'decode_checkpoint_master_box_v1',(321,'lanes'):'decode_checkpoint_lanes_box_v1',
(321,'purePlan'):'plan_pool_v1_pair_forest_checkpoint_v1',(321,'encodeMaster'):'encode_pool_v1_pair_forest_master_v1',(321,'encodeCheckpoint'):'encode_pool_v1_pair_forest_checkpoint_v1',
(326,'encode'):'encode_pool_v1_pair_forest_lane_state_v1',(294,'encode'):'encode_pool_v1_nullifier_marker',
(294,'canonicalNullifier'):'canonical_nullifier_encoding',(294,'address'):'pool_v1_pair_forest_nullifier_marker_address',
(294,'classify'):'classify_nullifier_marker_account_v1',(349,'encode'):'encode_pool_v1_pair_forest_terminal_request_v1'}
for key,name in expected.items():
 matches=[r for r in inv['rows'] if r['function'].split('::')[-1]==name]
 assert len(matches)==1,(key,name,[r['id'] for r in matches])
 M[key[0]][key[1]]=int(matches[0]['id'].split(':')[1])

kernel=json.loads(lzma.open(E.parent/'ledger25-20261111/NMQ_KERNEL_STATEMENTS.json.xz').read())

def header(root):
 if not root:return None
 if isinstance(root,list):return [header(x.get('root') if isinstance(x,dict) else x) for x in root]
 if isinstance(root,dict):return header(root.get('root'))
 if root in kernel:return dict(kernel[root],authority='ledger25 NMQ_KERNEL_STATEMENTS.json.xz',meaning='Exact replayed kernel statement; model/domain definitions retain their canonical owners')
 short=root.split('.')[-1]
 candidates=[]
 for folder in ['pc-helpers1-20261110','pc-helpers2-20261110','pc-deposit-children1-20261110','pc-deposit-children2-20261110','pc-terminal-children1-20261110']:
  for p in (E.parent/folder).glob('*.lean'):
   t=p.read_text()
   if ('namespace '+root.split('.')[0]) not in t:continue
   m=re.search(r'(?:theorem|lemma)\s+'+re.escape(short)+r'\b',t)
   if m:
    end=t.find(':=',m.start());candidates.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),statement=t[m.start():end].strip()))
 return candidates or dict(root=root,statement_location='Merged supplier ledger/source; inspect full kernel statement before installation')

def fields(text,alias=False):
 m=re.search(r'structure Children where\n(.*?)(?=\n(?:def |/--|abbrev |end ))',text,re.S)
 # Comments may contain /-- before another field; parse until the next top-level declaration.
 if 'structure Children where' in text:
  body=text.split('structure Children where\n',1)[1]
  end=re.search(r'^\S',body,re.M)
  body=body[:end.start()] if end else body
  return re.findall(r'^  ([A-Za-z][\w]*) : (.*)$',body,re.M)
 if 'abbrev Children := PCM.Vault.Children' in text or 'PCM.Vault.Children)' in text:
  return fields((E/'PCM_Vault.lean').read_text())
 return []
V={'ownedAccount':392,'mint':386,'token':387,'vaultAddress':391,'authorityAddress':390,'storedBumpMatches':379}
out=[]
for p in sorted(E.glob('PCM_Spec_POOL_*.lean')):
 n=int(p.stem.rsplit('_',1)[1]);fs=fields(p.read_text())
 for name,ty in fs:
  callee=(V if n in [388,389,395,396] else M.get(n,{})).get(name)
  assert callee is not None,(n,name,ty)
  rid=f'POOL:{callee:03d}';s=sup[rid];closed=s['status']=='CLOSED' and s['root']
  flag='MISSING-CHILD-LEMMA' if closed else 'OPEN-ROW'
  out.append(dict(slot=f'POOL:{n:03d}.Children.{name}',type=ty,kind='child-law' if 'Child ' in ty else 'getter/environment',supplier=s,exact_statement=header(s['root']),classification=flag,needed_lemma=f'PCM_adapter_{n}_{name}' if closed else None,domain_clauses=s['clauses'],discharged_by=f'POOL:{n:03d} at this SAME source call; representation by its native cut/entry admission',representation='PCM/RSL views to the supplier\'s exact emitted copies; scalar and fixed-array lengths; full error constructor maps; account-cell/lamport identities; ordered visible-event and abort-prefix projection',supplied=False))
# Typed decoder slots are function parameters rather than Children fields.
for n,callee in [(311,310),(312,306),(313,307),(314,207),(304,305),(337,209),(356,356),(357,357)]:
 s=sup[f'POOL:{callee:03d}'];closed=s['status']=='CLOSED' and s['root']
 out.append(dict(slot=f'POOL:{n:03d}.Decoder/SDK',kind='decoder/environment',supplier=s,exact_statement=header(s['root']),classification='MISSING-CHILD-LEMMA' if closed else 'OPEN-ROW',needed_lemma=f'PCM_adapter_{n}_decoder' if closed else None,domain_clauses=s['clauses'],discharged_by=f'POOL:{n:03d}; same input and writable flag (312 true, 313 false, 304 generic decoder true)',representation='Complete Result, all state/effects and stopped prefixes; Box site belongs to the caller wrapper',supplied=False))
# RSL PoolLib is authoritative field-for-field; reuse the merged LIB0 inventory.
lib0=json.loads((E.parent/'lib-map-20261107/LIB0_MAP.json').read_text())
for f in lib0['fields']:
 if f['struct']!='PoolLib':continue
 out.append(dict(slot='RSL.PoolLib.'+f['field'],kind=f['cls'],supplier=f.get('supplying',[]),exact_statement=f,classification='MISSING-CHILD-LEMMA',needed_lemma='PCM_shared_'+f['field'],domain_clauses='Exactly the LIB0/RSL rev3 supplier clauses, including returned-value reservation functionality where reached; never False or a stronger caller precondition',discharged_by='Pool owner at the same argument; RuntimeEntrypointAdmission-Pool for cell identity; EnvRep for the one headline reservation',representation=f['adapter'],supplied=False))
# Explicit runtime/representation slots, never implicit trust or stand-ins.
for name,owner,note in [
('RuntimeCpiAccountView',330,'ADDED-LEAD; unpassed keys frame only, passed contents unconstrained; not counters/handles/readonly'),
('RuntimeReturnData',348,'named runtime law; SAME producer/program/context and read chronology are caller obligations'),
('RuntimeReturnDataClear',348,'named empty-clear runtime law, separate from nonempty return-data law'),
('RuntimeCpiReadonlyEntry7',348,'PENDING/UNUSED; no instantiation is allowed'),
('RcCloneAndDrop',382,'NLF excludes Rc semantics; clone-overflow stopped sites are named, no native strong-count/drop frame is supplied'),
('ReturnedVecCapacity',348,'bytes alone cannot select into_boxed_slice shrink; preserve capacity/ownership from the actual get_return_data Vec'),
('RuntimeEntryCells',328,'valid/freshGuards/noExternalBorrows/liveAccount/counterZero/sharedCellsOnlyEqualKeys/duplicateKeysShareCell at entry only'),
('LamportCellsAndBorrow',333,'separate cell identity and infallible-borrow aborts; no data-only NLF law silently supplies them'),
('CpiBorrowCounterAndHandleFrame',330,'not in RuntimeCpiAccountView; caller/native SDK obligation remains OPEN'),
('ReservationBinder',330,'RSL.Env.reservation bound to the single headline NP6 reservation via EnvRep; no second channel')]:
 out.append(dict(slot='Representation.'+name,kind='environment/representation',supplier=dict(row=f'POOL:{owner:03d}',status='OPEN',root=None),exact_statement=note,classification='OPEN-ROW',needed_lemma=None,domain_clauses=note,discharged_by=f'Native/representation owner of POOL:{owner:03d}; not assumed by PCM',representation=note,supplied=False))
# The verifier slot is a composition, never a Root0-unconditional instance.
verifier=dict(slot='VerifierCPI.330/348',kind='composed top-level supplier',supplier=['NMN_064.root','NNC_064Weak','NNC_BindingRoot','TCK_REPORT option B / Realizes / RZ-STATE'],classification='OPEN-ROW',row='POOL:348',exact_statement='NMN_064.Domain: proofExtent=57607, checkpointExtent=1768, publicBound<=1880, Root0 checkpoint proof. Use the NNC Root0-free weak law first; derive Root0 OR the existing E_rec on the SAME realized execution; only then use NMN_064.root in the Root0 branch. Both internal Outcome bad and the outer event are E_rec, charged once.',domain_clauses=['57607 proof bytes','1768 checkpoint bytes','public <=1880','Root0 only on the derived branch, NEVER as an unconditional caller assumption'],discharged_by='Exact Pool CPI slice/entry/statement association plus Stream A selected weak/option-B top; Root0 not checked by frozen Rust',representation='Exact metas/infos/order, selected program, proof suffix/checkpoint/public bytes, full errors and effects, runtime context; readonly-entry law remains PENDING/UNUSED',supplied=False)
out.append(verifier)
report=dict(schema='PCM_SLOT_MAP_V1',supporting_only=True,row_credit=0,spec_freeze_sha256=hashlib.sha256((E/'PCM_SPEC_FREEZE.json').read_bytes()).hexdigest(),slots=out,counts={k:sum(r['classification']==k for r in out) for k in ['MISSING-CHILD-LEMMA','OPEN-ROW','SPEC-ERROR']},gate='Required combined NMQ/LIB/NLF/Stream-C gate pending; supplier packets are not silently reclassified as PCM-validated',findings=['Forbidden-origin context quarantine PCM_BLOCKED_CONTEXT.json; clarification pending','LIB_REMAINING: shared L-star is externally ready as LIBB_PoolLib.library but its completed V0-star/weak registration is not in the provided LIB bundle; consume it read-only when exported','Pool row numbers are distinct from TAS verifier entry row numbers; typed physical occurrence adapter is required'])
(E/'PCM_MAP.json').write_text(json.dumps(report,indent=1)+'\n')
lines=['# PCM Pool slot map','', 'Supporting work only; no row credit. All unfilled slots have exactly one prescribed classification. A supplier packet marked CLOSED below is still subject to PCM combined-import/revalidation; no unvalidated packet is promoted.', '', '| Slot | Supplier | Classification | Needed bridge / caller |','|---|---|---|---|']
for r in out:
 s=r['supplier'];label=(s.get('row','')+' '+str(s.get('root') or '')) if isinstance(s,dict) else str(s)
 lines.append('| '+r['slot']+' | '+label.replace('|','/')+' | '+r['classification']+' | '+str(r.get('needed_lemma') or r.get('discharged_by','')).replace('|','/')+' |')
lines += ['', 'Exact source statements, original domains, representation details and domain-discharge owners are in PCM_MAP.json. Needed-lemma names are obligations, not declarations claimed to exist. No relation/image-of-Cut is installed as a child law.', '', verifier['exact_statement'], '', 'Shared-library delivery dependency: '+report['findings'][1], '', 'Target not yet established.']
(E/'PCM_MAP.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(slots=len(out),counts=report['counts'])))
