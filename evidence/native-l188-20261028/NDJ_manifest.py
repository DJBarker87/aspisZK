"""Deterministic release audit report. Generation does not launch any prover."""
from pathlib import Path
import json,hashlib,lzma,re,sys
E=Path(__file__).resolve().parent;R=E.parents[1]
FROZEN='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def raw(p):
 p=Path(p);return lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes()
def obj(p):return json.loads(raw(R/p))
def logaudit(a,rootmodule):
 receipt=obj('evidence/native-l188-20261028/'+a+'/receipt.json')
 lines=(E/a/'stdout.log').read_text().splitlines();graph={};kernels=[];roots=[];axioms=[]
 for l in lines:
  if l.startswith('NDJ_IMPORT '):
   d=json.loads(l[11:]);graph[d['module']]=d['imports']
  elif l.startswith('NDJ_ROOT '):roots.append(json.loads(l[9:]))
  elif l.startswith('NDJ_KERNEL '):kernels.append(json.loads(l[11:]))
  elif l.startswith('NDJ_IMPORT_AXIOMS '):axioms=json.loads(l[18:])
 seen=set()
 def visit(m):
  if m in seen:return
  assert m in graph,('missing actual import header',m)
  seen.add(m)
  for n in graph[m]:visit(n)
 if receipt['exit_status']==0:visit(rootmodule)
 return dict(attempt=a,target=rootmodule,exit_status=receipt['exit_status'],wall_seconds=receipt['wall_seconds'],peak_rss_kib=int(receipt['peak_rss_kib']),swap=int(receipt['swaps']),source_revision=receipt['source_revision'],audit_reached=receipt['exit_status']==0,command=receipt['command'],limits=receipt['limits'],print_axioms=receipt['print_axioms'],roots=roots,kernels=kernels,closure_modules=sorted(seen),closure_module_count=len(seen),import_wide_axioms=sorted(axioms),import_wide_nonstandard_axioms=sorted(set(axioms)-STANDARD))
def trust():
 reachable=set(obj('evidence/replay-deployed2-20261027/RPx_reachable-constants.json'))
 s=(R/'evidence/native-elfpins-20261028/NCY_TRUST_INVENTORY_DRAFT.md').read_text();out=[]
 for l in s.splitlines():
  if not l.startswith('| ') or l.startswith('| Field'):continue
  fields=[v.strip() for v in l.strip('|').split('|')]
  assert len(fields)==4,fields
  name,scope,authority,kind=fields
  row=dict(name=name,scope=scope,authority=authority,classification=kind,headline_use='retained boundary or interface as classified; historical/derived/data rows are not independent assumptions',nonvacuity_use='not an explicit hypothesis of JHx_Joint.source; exact installed definitions/library base only')
  if name.startswith('Unadopted / open'):
   row['scope']='Historical full-account persistence, arbitrary unsafe equivalence, incomplete caller domains/trace joins, D188-P2 gaps and import-only nonstandard axioms remain unadopted/open. FixturePdaRuntime is separately ADOPTED below.'
   row['classification']='OPEN findings, no blanket trust credit'
  if name.startswith('Game '):row['classification']='13 G clauses + L154 parameter, not external trust'
  if name.startswith('P7 SBF'):
   row['scope']+=' NDC: 62 exact warned instances / 34 identities omitted; 102 function/ELF rows. Linked try_from_fn direct negative r10 operands 256,168,168; all linked direct negative r10 operands at most4096. Direct-operand evidence only, not derived-pointer/alias/callee bounds. Validator executable/configuration and virtual_address_space_adjustments activation unpinned; cached runtime archive authentication unavailable.'
  if name.startswith('Standard logical'):row['nonvacuity_use']='standard logical base used; each root audited separately'
  if name.startswith('Pinned Lean/'):row['nonvacuity_use']='pinned library/object base used; separate forest, no shared-environment success'
  if 'RuntimeSyscall.returningValue' in name:row['nonvacuity_use']='existing runtime SHA value row underlies fixture PDA runtime interpretation; the 453 SHA equations and seven PDA digests are proved, not new SHA trust'
  if name.startswith('`AspisR1.'):
   key=name.strip('`');row['headline_projection_reachable_in_pinned_RPx']=key in reachable
   row['headline_use']=('kernel-reachable field/interface; '+row['headline_use']) if key in reachable else 'Not independently used as a headline field law; retained historical/derived inventory classification only'
  if name.startswith('Unadopted / open'):row['headline_use']='NONE: unresolved/unadopted findings, not trust'
  out.append(row)
 out.append(dict(name='FixturePdaRuntime',scope='Exactly the seven fixture calls master, checkpoint, lane, registry, registryProgramdata, entry, verifierProgramdata: base.op38 agrees with JHs_PDA.derive under solana-pubkey2.4.0 valid readable seeds/program ID, disjoint output and sufficient compute. Ordered seeds + program ID + ProgramDerivedAddress; runtime SHA row supplies value; curve25519-dalek4.1.3 decompression, including noncanonical Y/sign semantics. Writes digest/returns0 off curve, InvalidSeeds1 on curve. Invalid memory, traps, exhausted compute, unlisted calls and other effects excluded. No digest equation, off-curve proof, caller acceptance or artifact identity supplied by this row.',authority='design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md late delegated adoption; lean/JHu_FixturePdaRuntime.lean; JHs_TRUST_PROPOSAL.md',classification='ADOPTED under lead delegation, REVERSIBLE, non-vacuity only',headline_use='NONE: soundness quantifies op38 under ruling(s)',nonvacuity_use='sole remaining propositional hypothesis of JHx_Joint.source; exact seven calls only'))
 return out
GAMES=[('Rc5_G001','game.consecutive.1','p.next t u'),('Rc5_G002','game.consecutive.2.1','e1 = entry p t'),('Rc5_G003','game.consecutive.2.2','e2 = entry p u'),('Rc5_G004','game.checkpoint.1','TX1 layout handle2 key = TX2 layout handle6 key'),('Rc5_G005','game.checkpoint.2.1','CPS_PhysicalKey.key e1 2 = CPS_PhysicalKey.key e2 6'),('Rc5_G006','game.checkpoint.2.2','checkpoint key is not in p.intervening t u'),('Rc5_G007','game.parent','success p t = true'),('Rc5_G008','game.recorded.1.1','p.copied t = saved'),('Rc5_G009','game.recorded.1.2.1','p.actions t = sourceActions'),('Rc5_G010','game.recorded.1.2.2','TX1 runtime Executes from actual afterCopy state with sourceActions and actual parent tentative/events'),('Rc5_G011','game.recorded.2','TX2 runtime Executes from cached bank u with actual actions/parent tentative/events'),('L083','root first wrapper antecedent','first native1 copy allocator e1 verifier data1 state1 = ok (.Ok (saved,post1,state1′))'),('L084','root second wrapper antecedent','second native2 allocator e2 verifier data2 slot state2 = ok (.Ok (post2,state2′))')]
BLOCKERS=[
'Final coherent shared-environment replay: NDJ_R001 duplicate declaration import failure; separate forests do not satisfy this gate.',
'D188/native extraction association and S10 completeness: unresolved A0–A8/D188-P2 source/body/carrier/dictionary/feature associations and required opaque-leaf native bridges; every composed NCZ row remains OPEN, including same-execution caller domains, ordered effects and rejected-prefix accounting.',
'Strict import-wide logical audit: nonstandard imported axioms remain unadopted/root-unreachable; root standard-only does not resolve F-AXIOM.',
'Joint witness-to-headline installed-world/producer reconciliation: JHx_Joint.source is a conditional concrete fixture in its separately pinned environment, not a jointly replayed instantiation of all headline trust/game hypotheses.',
'Runtime/ELF execution association: validator executable/source/build-feature pins, execution budget, active feature/stack-gap configuration and authenticated runtime source provenance are not established; no live loaded-program/readback/upgrade-authority association is claimed.'
]
RELEASE='Machine-checked predecessor proofs establish the installed frozen3 RPx_Deployed.deployed model theorem and the JHx_Joint.source real-byte fixture witness in separately pinned object forests; this packet audits their exact statements and reachable logical axioms, and reuses NCR/NCY reproductions of the default, devnet and Pool ELFs built from frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 with lock 5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef. Interpretation for those artifacts retains the named SDK admission/borrow, TrustedStd, private Allocator, data-only RuntimePersistence, runtime/loader/ABI, returning runtime SHA, P1 ideal-oracle realization, narrowed D188/extraction, amendment-five native semantic transport, P6/Kani under amendment-four/K-1/KMX/K-2 restrictions, P7 compiler/library base and adopted game/model rows; FixturePdaRuntime is adopted reversibly for non-vacuity only. For Q=Q0+Q1 at most7388980242446479800895501321004157112314840375, the model per-attempt failure bound is at most(Q+1)/2^100, with L154 the issued-query-budget parameter counting duplicates and rejected prefixes, not a discharged premise; at Q=0 the exact bound is strictly below2^-100. This establishes neither an unlimited repeated-attempt/work-normalised security level nor privacy, extraction effectiveness/cost, custody, availability, complete native refinement or live deployment identity. The target not yet established: the five obligations listed in remaining_obligations are missing; extraction remains TRUST, narrowed by D188 and amendment five, and native coverage is partial support only.'
def derive():
 audits=[]
 for a,root in [('NDJ_R002','RPx_Deployed'),('NDJ_R003','JHx_Joint'),('NDJ_R004','JHx_Joint')]:
  if (E/a/'stdout.log').exists():audits.append(logaudit(a,root))
 passing=[a for a in audits if a['exit_status']==0]
 head=next((a for a in passing if a['target']=='RPx_Deployed'),None);joint=next((a for a in passing if a['target']=='JHx_Joint'),None)
 if head:assert head['kernels'][0]==obj('evidence/replay-deployed2-20261027/RPx_Deployed.kernel-expr.json'),'headline kernel expression changed'
 combined=obj('evidence/native-l188-20261028/NDJ_R001/receipt.json')
 combined_result={k:combined[k] for k in ['attempt','module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','limits']}
 sourcepins=obj('evidence/native-elfpins-20261028/NCY_SOURCE_PINS.json')
 elf=[]
 for mode,ref in [('default','evidence/native-elfscope-20261028/NCR_B003-receipt.json'),('devnet','evidence/native-elfpins-20261028/NCY_B001-receipt.json'),('pool','evidence/native-elfpins-20261028/NCY_B002-receipt.json')]:
  receipt=obj(ref);res=receipt if mode=='default' else receipt['result'];assert receipt['exit_status']==res['build_exit']==0 and res['match']
  elf.append(dict(mode=mode,sha256=res['artifact_sha256'],bytes=res['bytes'],receipt=ref,build_wall_seconds=res['build_wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps'],source_revision=receipt['actual_task_revision'],print_axioms=receipt['print_axioms']))
 coverage=obj('evidence/native-l188-20261028/NDJ_COVERAGE.json')
 coverage['authoritative_refresh']=obj('evidence/native-l188-20261028/NDJ_NDK_RESULT.json')
 delta_counts={}
 for path,delta in coverage['deltas'].items():
  rows=delta.get('members',delta.get('functions',delta.get('closures',[])))
  delta_counts[path]=sum(r.get('local_status',r.get('status','')).startswith('CLOSED') for r in rows)
 assert sorted(delta_counts.values())==[6,7,8],delta_counts
 host=obj('evidence/native-l188-20261028/NDJ_HOST_VERIFICATION.json.xz')
 kernel=(R/'evidence/replay-deployed2-20261027/RPx_Deployed.kernel.lean.txt').read_text()
 out=dict(schema_version=1,status='L188 OPEN; target not yet established',headline='AspisR1.RPx_Deployed.deployed',kernel_statement=kernel,kernel_statement_sha256=sha(kernel.encode()),kernel_statement_note='Historical printed comment names FJv_Deployed; exact type is authoritative and NDJ_R002 compares kernel Expr with RPx audit.',query_parameter=dict(row='L154',meaning='Q=Q0+Q1, issued queries for all H, duplicates and rejected prefixes included; parameter, not discharge',max_queries=7388980242446479800895501321004157112314840375,bound='failureModel ≤ total(Q) ≤ (Q+1)/2^100 within range; total(0)<2^-100',total='(Q+34)*15/2^109 + 6*(Q+1161)^2/2^256 + 6*(Q+2965)^2/2^256 + 2^-126 + 2^-454'),game_clauses=[dict(id=i,path=p,meaning=m) for i,p,m in GAMES],frozen_source_revision=FROZEN,frozen_lock_sha256=sourcepins['files']['Cargo.lock'],frozen_source_pins=sourcepins['files'],trust_inventory=trust(),trust_common_qualifications='All SDK laws are only under the exact L.related, Valid, counter/enabledness and lifetime conditions in L8a_008; preserve reply AND next heap; solana-account-info2.3.0/frozen lock. Excluded: Ref clone/map_split/leak, realloc, Rc clone/free, lamport borrows, CPI, reentrancy and concurrency. No SDK row supplies caller success, proof bytes, output, oracle history or a child/source join. Exact installed dictionaries/worlds are shared as in the full kernel type.',elf_reproductions=elf,build_recipe='cargo-build-sbf3.1.13/platform-tools1.52/rustc1.89.0-dev/LLVM20.1.7; release opt-level3 sbpf-solana-solana; offline locked -j4; target link-arg --threads=4; exact per-mode features/IDs in NCR_FEATURE_TABLE and Low2_build_manifest',audit_attempts=audits,combined_attempt='NDJ_R001',combined_replay=combined_result,combined_replay_success=False,separate_roots_pass=bool(head and joint),union_module_count=len(set().union(*(set(a['closure_modules']) for a in passing))),closure_count_scope='union of separately audited root import forests, includes trusted libraries; not a successful common environment',coverage=coverage,frontier_delta_local_packet_counts=delta_counts,evidence_index='evidence/native-l188-20261028/NDJ_EVIDENCE_PINS.json',host_verification=dict(receipt='evidence/native-l188-20261028/NDJ_HOST_VERIFICATION.json.xz',checked_files=host['checked_files'],exit_status=host['exit_status'],errors=host['errors']),extraction_status='TRUST — narrowed D188 and amendment five; native evidence partial support; NEVER discharged',remaining_obligations=BLOCKERS,release_statement=RELEASE,security_contract_changed=False,budget=dict(normal_lean_used=3,normal_lean_limit=6,agg16_used=int((E/'NDJ_R004/receipt.json').exists()),agg16_limit=1,kani_used=0))
 assert out['kernel_statement_sha256']=='8ae0107f9dbb7374135912ff9dda3597ad0096023d0deed471b0cd4dcf305523'
 return out

def markdown(d):
 lines=['# L188 release manifest','',d['release_statement'],'','## Replay and logical audit','',d['status']+'. The combined attempt failed before any axioms audit. See NDJ_IMPORT_FINDING.md. Separate successful roots retain their own object selections; these are cached-object audits, not fresh dependency/library recompilations.','', '| Target | Attempt | Exit | Wall s | Peak RSS KiB | Swap | Root closure modules |','#SEP#']
 lines[-1]='|---|---|---:|---:|---:|---:|---:|'
 for a in d['audit_attempts']:
  lines.append(f"| {a['target']} | {a['attempt']} | {a['exit_status']} | {a['wall_seconds']} | {a['peak_rss_kib']} | {a['swap']} | {a['closure_module_count']} |")
  lines+=['',f"Source revision `{a['source_revision']}`; #print axioms: `{' ; '.join(a['print_axioms']) or 'not reached'}`. Strict import-wide nonstandard axiom count: {len(a['import_wide_nonstandard_axioms'])}.",'']
 lines += [f"Complete separately audited closure union: **{d['union_module_count']} modules**. Exact graphs, all nonstandard names and kernel expressions are in JSON. F-AXIOM is retained, not accepted. All artifact/object and source pins are checked by NDJ_validate.py; NDJ_EVIDENCE_PINS.json joins all cited packet bytes and NDJ_HOST_VERIFICATION pins copied/original objects, sources, tools and the three retained ELFs.",'','## Final trust inventory','', 'Rows inherited verbatim in scope from NCY, with the late adoption and NDC qualifications below. No new 83T/89T recount or premise removal is claimed. Repeated uses share the exact worlds/dictionaries of the kernel statement. Historical, derived, data and G rows are not additional trust.','', d['trust_common_qualifications'], '', '| Boundary | Exact retained scope | Authority / classification | Root use |','|---|---|---|---|']
 for t in d['trust_inventory']:lines.append('| '+t['name']+' | '+t['scope']+' | '+t['authority']+'; '+t['classification']+' | Headline: '+t['headline_use']+'; joint: '+t['nonvacuity_use']+' |')
 lines += ['','## Frozen artifacts and coverage','',f"Frozen source `{d['frozen_source_revision']}`; Cargo.lock `{d['frozen_lock_sha256']}`. {d['build_recipe']}. Exact dependency/config/generated-source/tool executable pins are joined through NCY_SOURCE_PINS, Low2_build_manifest, NCR_RELEASE_CFG, NCR_FEATURE_TABLE, NCS and KNG feature/property audits, and NDC stack receipts.",'']
 for x in d['elf_reproductions']:lines.append(f"- {x['mode']}: `{x['sha256']}`, {x['bytes']} bytes; successful reproduction `{x['receipt']}` reused. Compiler semantics P7 remains trust.")
 c=d['coverage']['authoritative_refresh']['coverage'];a=c['all_rows'];u=c['unique_functions']
 lines+=['',f"NCZ snapshot: {a['rows']} reached occurrences, {u['count']} unique functions. Local occurrences: {a['local_bridge_status']}; unique: {u['local_bridge_status']}. Unconditional bridges: 0. Composed OPEN: 587; composed closed: 0. NDD adds seven qualified local packets, NDF six and NDG eight. The newly merged authoritative NDK refresh explicitly reviews/adopts these21 domains into30 transaction occurrences; its unchanged full reconstruction and summary plus original NCZ structural invariants are rerun by NDJ_NDK.py. The old NCZ213/370/4 baseline and separate deltas are retained for comparison. This is qualified local support, never composed closure. Refreshed report corpus uses the pinned merged revision in NDJ_COVERAGE.json. The baseline and refreshed research snapshots were revalidated through unchanged NCZ collect/validate_invariants with an explicit immutable Git adapter; this worktree remains on its own older branch. Direct invocation at current HEAD correctly rejected the changed report corpus; no failure was suppressed.",'','`extraction` remains **TRUST**, narrowed by D188 and amendment five. Native packets supply partial support only. K-2/rule14 passes remain quarantined (including mark/release-observer paths); KNG/KNF replacements do not rehabilitate historical pointer receipts. K-1 copy credit requires exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 and matched failing controls; contracts require amendment-four fidelity controls.','', '## Game and query parameter','', 'Eleven expanded game conjuncts plus two wrapper antecedents; these are experiment/acceptance conditions, not external trust. Exact binders and quantifiers remain in the full type below.','']
 for g in d['game_clauses']:lines.append(f"- {g['id']} (`{g['path']}`): {g['meaning']}.")
 lines += ['', 'L154 is Q=Q0+Q1 for every induced oracle H, counting duplicate/rejected issued calls. Within the exact maxQueries range in JSON, failureModel ≤ total(Q) ≤ (Q+1)/2^100. total(Q)=(Q+34)*15/2^109+6*(Q+1161)^2/2^256+6*(Q+2965)^2/2^256+2^-126+2^-454. At Q=0, total(0)<2^-100. No unlimited-campaign or work-cost inference.','', '## Missing release obligations','']
 lines += [str(i)+'. '+b for i,b in enumerate(d['remaining_obligations'],1)]
 lines += ['','## Complete headline kernel type','',f"SHA256 `{d['kernel_statement_sha256']}`. The historical comment names FJv_Deployed; the RPx kernel Expr comparison verifies the adopted headline has this exact type.",'','```lean',d['kernel_statement'].rstrip(),'```','']
 return '\n'.join(lines)
if __name__=='__main__':
 d=derive();(E/'NDJ_RELEASE_MANIFEST.json').write_text(json.dumps(d,indent=2,sort_keys=True)+'\n');(E/'NDJ_RELEASE_MANIFEST.md').write_text(markdown(d));print(d['status'])
