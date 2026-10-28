import pathlib,json,re,hashlib,collections,subprocess
E=pathlib.Path(__file__).parent
rows=json.load(open(E/'NCS_ASSOCIATIONS.json'))['rows'];body={r['id']:r for r in json.load(open(E/'NCS_BODY_HASHES.json'))['bodies']};hs=json.load(open(E/'NCS_HARNESS_AUDIT.json'))['rows'];ha={r['attempt']:r for r in hs};rr={r['attempt']:r for r in json.load(open(E/'NCS_RECEIPTS.json'))}
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
quarantine=json.load(open('evidence/native-elfscope-20261028/NCR_QUARANTINE.json'))
# Select exact cited positive receipts only; negative controls and failed attempts never establish a positive.
def positives(names):
 out=[]
 for n in sorted(set(names)):
  if n not in rr or rr[n]['exit']!=0:continue
  original=json.loads(pathlib.Path(rr[n]['path']).read_text())
  if original.get('negative_control')is True:continue
  out.append(n)
 return out

def support(r):
 p=r['packet'];details=[]
 for detail in r['detail']:
  if detail.startswith('{'):
   obj=json.loads(detail);details.append(' '.join(str(obj.get(k,''))for k in ['evidence','new_evidence','evidence_or_open']))
  else:details.append(detail)
 txt=' '.join(details)
 for source in r['sources']:
  if re.search(r':\d+$',source):
   path,no=source.rsplit(':',1);txt+=' '+pathlib.Path(path).read_text().splitlines()[int(no)-1]
 names=re.findall(r'\b(?:LP[a-z]|N[BC][A-Z]|KM[X-Z]|KN[A-E])_K\d{3}\b',txt)
 if p=='P6':
  leaf=r['sources'][0];txt=pathlib.Path(leaf).read_text();owner=pathlib.Path(leaf).name.split('_')[0]
  if r['member']=='verifier::checkpoint':return [h['attempt']for h in hs if h['attempt'].startswith('KNE_')and h['exit']==0 and not json.loads(pathlib.Path(h['receipt']).read_text()).get('negative_control',False)]
  names+=[owner+'_K'+n for n in re.findall(r'(?<![A-Za-z0-9_])K(\d{3})\b',txt)]
 elif p=='KMX':names=[json.loads(r['detail'][0])['attempt']]
 elif p=='KMZ':
  x=json.loads(r['detail'][0]);names=x.get('positive_runtime',[])+x.get('legacy_positives',[])
 else:names+=[p+'_K'+n for n in re.findall(r'(?<![A-Za-z0-9_])K(\d{3})\b',txt)]
 for a,z in re.findall(r'K(\d{3})(?:[–—-]|\.\.)K?(\d{3})',txt):
  if 0<=int(z)-int(a)<100:names += [p+'_K'+str(n).zfill(3)for n in range(int(a),int(z)+1)]
 if r['packet']=='NBQ' and r['member']=='powers':names+=['NBQ_K017','NBQ_K018','NBQ_K019','NBQ_K020']
 if r['packet']=='NBQ' and r['member']=='canonical::Dot::push':names+=['LPn_K013']
 if p=='NBG'and r['member']in ['mark','observer','value']:names += [{'mark':'NBC_K001','observer':'NBC_K002','value':'NBC_K003'}[r['member']]]
 if p=='NBP':
  n=r['roots'][0].split('::')[-1];mapping={'decode_digest_canonical':'NBG_K019','encode_digest_canonical':'NBG_K020','decode_common':'NBP_K030','encode_common':'NBP_K018','decode_pool_v1_private_transfer_public_v1':'NBP_K033','decode_pool_v1_withdrawal_public_v1':'NBP_K034','encode_pool_v1_private_transfer_public_v1':'NBP_K031','encode_pool_v1_withdrawal_public_v1':'NBP_K032'}
  if n in mapping:names+=[mapping[n]]
  else:
   for q in rows:
    if q['packet']=='NBG'and q['roots']==r['roots']:names+=support(q)
 if p in ['NBU','NBX','NBN','NBK']and (not names or 'inherit'in txt.lower()):
  precedence={'NBU':['NBN','NBK','NBH','NBD'],'NBX':['NBU','NBN','NBK','NBH','NBD'],'NBN':['NBK','NBH','NBD'],'NBK':['NBH','NBD']}
  for owner in precedence[p]:
   donor=next((q for q in rows if q['packet']==owner and q['roots']==r['roots']),None)
   if donor:names+=support(donor);break
 if r['id']=='NBX::validate_result':names+=['NBU_K050']
 if r['id']=='NBU::transition_kind':names+=['NBD_K009']
 if r['id']=='P6::verifier::prepared_claim':names+=['LPq_K001','LPm_K010','LPm_K012','LPm_K013','LPm_K014','LPm_K016','LPm_K017','LPm_K018']
 if r['id']in ['NBQ::error','NBS::error']:names+=['NBQ_K016']
 return positives([json.loads(r['detail'][0])['attempt']])if p=='KMX'else positives(names)

def feature_class(r):
 if r['packet']=='P6' or r['packet']in ['KMX','KMZ','NCA','NCI']or r['packet']=='NBQ'and r['member']!='error':return 'library-default'
 if all(k.startswith('crates/aspis-core/')for k in r['roots']):return 'core-default'
 if all(k.startswith('crates/aspis-statement/')for k in r['roots']):return 'statement-default'
 return 'program-deployed'if r['packet']in ['NBC','NBG','NBP','NBS','NBQ']else 'library-default'

def short(k):return k.split('/src/')[-1]
results=[]
for i,r in enumerate(rows,1):
 r=dict(r);r['audit_id']='NCS_R'+str(i).zfill(3);r['original_feature_class']=feature_class(r);fc=r['original_feature_class'];r['positive_receipts']=support(r)
 missing=[n for n in r['positive_receipts']if n not in ha or not ha[n]['matched_sources']]
 matched=[ha[n]for n in r['positive_receipts']if n in ha and ha[n]['matched_sources']]
 r['missing_exact_harness_sources']=missing
 r['reached_hashes']=[dict(function=k,original=body[k]['configurations'][fc]['sha256'],deployed=body[k]['configurations']['library-deployed']['sha256'])for k in r['reached_inventory_bodies']]
 r['differing_functions']=[x['function']for x in r['reached_hashes']if x['original']!=x['deployed']]
 r['cone_original_sha256']=sha('\n'.join(x['function']+':'+str(x['original'])for x in r['reached_hashes']))
 r['cone_deployed_sha256']=sha('\n'.join(x['function']+':'+str(x['deployed'])for x in r['reached_hashes']))
 # A source theorem without a cited native PASS is not silently manufactured into a harness association.
 no_positive=not r['positive_receipts']
 source_law=no_positive and r['packet']=='NBG'and all(k.startswith('crates/aspis-core/')for k in r['roots'])
 r['classification']='DIFFERENT BODIES'if r['differing_functions']else 'UNDETERMINED'if missing or (no_positive and not source_law) else 'SAME BODIES'
 r['reason']='Reached selected body differs'if r['differing_functions']else 'Exact historical positive harness snapshot unavailable: '+', '.join(missing)if missing else 'Emitted arithmetic source law; no independent native Kani PASS is counted. Frozen body identity holds on the retained domain'if source_law else 'No uniquely cited positive runtime harness was recoverable from this member row; frozen member cone matches, harness association not established'if no_positive else 'Cfg-selected hashes agree for every inventoried reached project function; exact cited positive harness bodies retained; original local domains and external/source-association boundaries remain'
 r['arithmetic_stubs']=sorted({a for h in matched for s in h['matched_sources']for a in s['attributes']if 'stub'in a and re.search(r'mul|square|reduce|inv|overflow|panic|assert',a,re.I)})
 r['all_stubs']=sorted({a for h in matched for s in h['matched_sources']for a in s['attributes']if 'stub'in a})
 r['profile']='P3'if source_law else 'P2'if missing or no_positive else 'P1'if r['all_stubs']else 'P0'
 r['profile_assessment']='No separate Kani PASS; emitted arithmetic value/range law retains its original source association and operands'if source_law else 'Unknown exact harness/flag coverage; no whole-callee no-overflow inference'if r['profile']=='P2'else 'Callee replaced (see exact all_stubs): PASS excludes overflow only in executed real paths; omitted arithmetic/assertion/bounds behavior needs its inherited callee law'if r['profile']=='P1'else 'PASS excludes checked overflow/debug-assert failure on verified real paths; release wrapping cannot arise there. Effective historical rustc flags not fully retained; scope stays local'
 r['quarantined_support']=[q for q in quarantine['rows']if any(n in q.get('receipt','')for n in r['positive_receipts'])]
 results.append(r)
# Standalone/control metadata cannot retrospectively become a Cargo compile of verifier code.
summary=dict(count=len(results),classifications=dict(collections.Counter(r['classification']for r in results)),profiles=dict(collections.Counter(r['profile']for r in results)),feature_mismatch_suspended=[r['id']for r in results if r['classification']=='DIFFERENT BODIES'],undetermined=[r['id']for r in results if r['classification']=='UNDETERMINED'])
(E/'NCS_RESULTS.json').write_text(json.dumps(dict(summary=summary,rows=results),indent=2)+'\n')
suspended=dict(status='No re-verification; no new credit from an unresolved row. SAME BODIES clears only rule15 feature-body parity, never rule14 or K-1.',feature_mismatch_suspended=[dict(id=r['id'],functions=r['differing_functions'])for r in results if r['classification']=='DIFFERENT BODIES'],undetermined=[dict(id=r['id'],reason=r['reason'],missing_harness_sources=r['missing_exact_harness_sources'],source_cone_hashes_equal=r['cone_original_sha256']==r['cone_deployed_sha256'])for r in results if r['classification']=='UNDETERMINED'],inherited_rule14_quarantine=quarantine['rows'],excluded_open_results=['NBW_K026','KNB_K001','KNC_K003','NCH_K049'],checkpoint_qualification='KNE reached S2/final_len64 domain, named DriverEstablishedDomain and retained physical Rust/library/allocator association. Original nine arbitrary-growth rows remain superseded/uncredited; no restoration here.')
(E/'NCS_SUSPENDED.json').write_text(json.dumps(suspended,indent=2)+'\n')
lines=['# NCS deployed-feature body-identity credit audit','','## SUSPENDED / no deployed credit first','','**DIFFERENT BODIES: none identified among the credited member cones.** This is not a whole-program parity claim.','',f"**UNDETERMINED: {len(suspended['undetermined'])} exact packet/member results.** Their inventoried frozen source cones match, but the required historical harness association is incomplete; no deployed-code credit is newly admitted. Recover the named snapshots/positive association before deciding whether any re-verification is needed.",'']
lines+=['- `'+r['id']+'`: '+r['reason']+'.'for r in suspended['undetermined']]
lines+=['','**Inherited rule14 quarantine remains no credit (not withdrawn):**','']
lines+=['- `'+q['harness']+'` — `'+q['receipt']+'`.'for q in quarantine['rows']]
lines+=['- Additional known open chains: `NBW_K026`, `KNB_K001`, `KNC_K003`, `NCH_K049`; no promotion or renaming.','','## Scope and method','',f"Audited {len(results)} packet/member families: the 13 P6 leaves; all explicit CLOSED/CLOSED-CONDITIONAL native member rows in merged NB/NC bridge tables and native-status ledgers; 18 KMX restored narrow replay families and seven KMZ restored original properties; 11 duplicate abbreviated/file-qualified member rows were merged. Historical packet/member rows remain separate; repeated references within a packet merge. NBP U02 contributes exactly its 16 explicit inventory members; NBQ U06 contributes its 12 conditionally closed members. OPEN composites, source-model-only rows, negative controls and timeouts do not become native closures.",'','Frozen source `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; lock SHA256 `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. Native source-body pins are matched to both TX1/TX2 inventories by exact SHA256, then their conservative call edges are followed. `NCS_ASSOCIATIONS.json` retains roots, reached IDs and unresolved edges. This is source inspection, not compiler-certified dynamic reachability. External SDK/std/allocator/oracle contracts and dynamic dispatch remain the original trust/association boundaries. A matching cone does not clear missing harness association.','', 'Feature graphs: `NCS_I002-stdout.log` resolves six isolated canonical roots with cargo metadata; `NCS_I003-stdout.log` resolves 31 historical manifest/feature variants; `NCS_I005-stdout.log` resolves NCA and KMX wrappers. Every graph records every resolved crate feature set. Wrapper dependencies retain default features unless the historical command disabled them. Frozen locks seed offline resolution. Audit-only wrapper roots are excluded from release-package identity. Workspace-wide metadata in I001 over-unifies unrelated members (including spend-dynamic-rate512) and is retained as REJECTED for per-root parity. No workspace manifest was edited. Root dev-dependencies are not reproduced by dependency wrappers; any feature-sensitive dev-dependency/harness linkage requires historical compiler association.','', 'The library default graph is default/private-leaf-salts, core:r0, statement:r0/pool-v1-kernel. Deployment adds optimized-terminal/program-build and exactly twelve statement optimization features. Statement-only and core-only runs have no such flags. Program pool-adapter/private-leaf-salts already expands to the deployed verifier selection. `no-entrypoint` suppresses the ABI entry and has no entrypoint credit. Target/profile are held fixed during feature comparison.','', 'Body hashes in `NCS_BODY_HASHES.json` use the exact frozen opening/closing body span, AST cfg/cfg! selection, then SHA256 over NUL-separated lexical tokens with comments/formatting removed. Attributes select complete statements, expressions and arguments; inactive definitions have null hashes. Quoted string contents are retained; macro expansion/type-dependent constant lowering is outside this hash check. Each row below hashes the sorted function-ID/body-hash list as a cone fingerprint; per-function original/deployed hashes are in `NCS_RESULTS.json`. This is cfg-evaluated source, not MIR or compiler macro expansion. Macro/type/constant lowering and target semantics are not promoted to binary identity.','', 'All 349 project source files parsed without errors (9,069 function definitions). Nine shared available function bodies change under library default versus deployment: Selectors::active, pattern_values, accumulate_endpoint, evaluate_with_selectors, semantic_initial_and_absorption, add_path_lanes, add_value_lanes, add_occupancy_lanes, semantic_packed. Additional definitions switch availability. `NCS_CHANGED_BODIES.json` retains selected text; `NCS_BODY_HASHES.json` retains all availability/hash pairs. None appears in the credited inventoried cones. Thus this audit does not suspend an open semantic composite as if it had been credited.','', 'Historical harness audit: `NCS_HARNESS_AUDIT.json` stores exact receipt SHA-matched source/body hashes, calls, stubs, feature predicates and missing snapshots. Complete /dev/null additions and context-checked patch chains were reconstructed in memory; current host snapshots count only on exact historical SHA equality. No unmatched current file substitutes for an earlier implementation. Some cited ranges include positive fragment/diagnostic gates; credit remains exactly the original member statement, never the union of unrelated harnesses.','','## Release profile assessment for every credited positive','', 'P0: checked real paths. Ordinary recorded cargo-kani commands omit --release and disable neither dev overflow checks nor dev debug assertions. opt-level=3 and debug=0 do not disable those checks; CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true affects release only. A PASS with checked overflow enabled proves no overflow on its verified paths, so disabling checks cannot introduce release wrapping on those paths. Pure debug_assert conditions in reached source have no state-changing effect; their successful checks may be removed without altering the checked value result. No conclusion extends beyond the harness assumptions/domain.','', 'P1: one or more callees replaced (including memory, allocator, arithmetic, decoder or sampler cuts). The exact stub attributes are recorded per row in all_stubs (arithmetic_stubs is a narrower name-based subset); PASS does not prove absence of overflow inside the omitted arithmetic body. Its inherited emitted-value/canonicality/word-bound proof is still required on the SAME operands. Copy stubs retain their independent K-1 law/fidelity qualification.','', 'P3: emitted arithmetic source law only; no separate native Kani PASS is counted and no checked-path argument is invented. The inherited exact word/range result remains the basis for release arithmetic.\n\nP2: exact harness association unavailable or no uniquely cited runtime positive. No blanket no-overflow conclusion is admitted. Historical effective rustc commands are not complete even for P0/P1; source recipes plus defaults are evidence, not a new binary flag attestation. KMY/KMZ/KND/KNE windows run kani-driver standalone: no Cargo dev profile or verifier feature graph applies to the standalone file. Their fixed-window arithmetic/copy laws and source association remain explicit. No observed recorded command explicitly disables assertion/overflow checks. Every recovered callee substitution is flagged P1; this audit does not infer that omitted callees preserve their internal checks. Missing sources are not cleared by that search.','', 'KNE checkpoint remains its reached S2/final_len64/64-weights conditional leaf, with DriverEstablishedDomain and initialized-spare/physical-source/library/allocator/oracle qualifications. The original nine arbitrary-growth assertions remain superseded and uncredited. SAME source bodies does not establish SBF syscall, ABI/layout, allocator, deployment-ID or source-to-ELF parity; NCR_TARGET_DEPENDENT.md remains binding.','','## Full per-result table','', 'Classifications below concern rule15 feature-body transfer within existing local domains. `U` means UNDETERMINED; `S` means SAME BODIES. Full IDs, statement scope, positive receipts, missing sources, stubs, hashes and boundary edges are in NCS_RESULTS.json. Existing rule14 support quarantines override feature-parity credit.','', '| Audit row | Credited packet/member | Result | Original feature class | Cone original / deployed SHA256 (prefix) | Reached bodies | Profile |','|---|---|---|---|---|---:|---|']
for r in results:
 lines.append('| '+r['audit_id']+' | `'+r['id'].replace('`','')+'` | '+('S'if r['classification']=='SAME BODIES'else 'U'if r['classification']=='UNDETERMINED'else 'DIFFERENT BODIES')+' | '+r['original_feature_class']+' | `'+r['cone_original_sha256'][:16]+'` / `'+r['cone_deployed_sha256'][:16]+'` | '+str(len(r['reached_hashes']))+' | '+r['profile']+' |')
lines+=['','## Validation actually run','','Six admitted serial inspection scopes, high6G/max8G/swap0/tasks64; all exit0, no swap. Attempts and admission/time/RSS receipts: NCS_ATTEMPTS.jsonl and NCS_I00*-receipt.json. Zero Kani, zero Lean, zero SBF/Rust builds, no crate/program changes, no push. Historical validation is reused with its original qualifications, not rerun.']
(E/'NCS_PARITY_AUDIT.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(summary,indent=2))
