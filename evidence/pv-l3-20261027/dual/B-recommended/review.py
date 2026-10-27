"""Check manually reviewed PC/source associations; static evidence, no execution."""
from pathlib import Path
import json,re,hashlib,time,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-l3-20261026');O=H/'dual-evidence/B-recommended';R=H/'dual-B-recommended';t=time.monotonic();cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
rec=json.loads((O/'receipt.json').read_text());inv=json.loads((O/'inventory.json').read_text());calls=json.loads((O/'calls.json').read_text());asm=(O/'selected-disassembly.txt').read_text();blocks={};pcs={}
for block in asm.split('\n\n'):
 lines=block.splitlines()
 if not lines:continue
 m=re.match(r'([0-9a-f]+) <(.*)> size=',lines[0])
 if not m:continue
 instructions=[]
 for line in lines[1:]:
  n=re.match(r'\s*([0-9a-f]+): (\S+)\s*(.*)',line)
  if n:pcs[n[1]]={'address':'0x'+n[1],'op':n[2],'args':n[3]};instructions.append(pcs[n[1]])
 blocks[m[2]]={'start':m[1],'instructions':instructions,'text':block}
def instructions(addresses):return [pcs[x] for x in addresses]
findings=[]
def add(id,path,anchor,addresses,kind,rows,condition):
 src=(R/path).read_text().splitlines();line=next(i for i,s in enumerate(src) if anchor in s)
 findings.append(dict(id=id,source_revision=rec['source_revision'],path=path,line=line+1,source_sha256=hashlib.sha256((R/path).read_bytes()).hexdigest(),source_context=src[max(0,line-2):line+4],instructions=instructions(addresses),classification=kind,ledger_rows=rows,honest_domain_obligation=condition))
h='crates/aspis-r1-cost-probe/src/host_semantic.rs';v='crates/aspis-r1-cost-probe/src/prover.rs';s='crates/aspis-r1-cost-probe/src/host_sumcheck.rs';p='crates/aspis-prover/src/state_only_hiding.rs';e='crates/aspis-prover/src/state_only_entropy.rs'
add('N1','crates/aspis-r1-cost-probe/src/ct_pole.rs','pub(crate) fn all_slots_clear',['bf8f3','bf93e','bf95a','bf960','bf967','bf96e','bf995','bf9be','bf9df','bf9ed','bfa13','bfa16','bfa19','bfa25','b5c5c','b5a1d'],'public geometry branches; secret operands in fixed SIMD compare/reduction; final verdict secret-dependent',['V357','V360','V373','V371'],'No limb-prefix Jcc in this scan. Final pole verdict R3 and source/machine joint law remain P; no whole-program claim.')
add('N2',p,'fn check_h1_padding_active',['13a08b','13a091','13a097','13a09c','13a149'],'secret-derived guard branches',['V354','V360','V373'],'Expected constant: active padding is all zero (first three JNE false, last JE true); inactive sum is zero (JNE false). Needs construction/caller invariant proof, not proved here.')
add('N3',h,'fn check_semantic_columns',['b4324','b4332','b4340','b434e','b43ba','b4420'],'secret-derived canonicality guard branches',['V357','V360','V373'],'Expected constant valid: canonical C1/D/G and fixed shape; JA false and decode-error JE false. Prove canonicality preserved through masking and field arithmetic and binds this caller.')
add('N4',v,'let audit=audit_masks',['a47a2','a47b1','a47bf','a47cd','a47db','9d835','9d8e5','9dab0','9dacf','9daf4'],'secret-derived mask audit guards; local comparisons use SETcc/SIMD',['V354','V360','V373'],'Expected constant valid: balanced counts 16/10 and D/G/H1 inactive sums zero; all listed owner error branches untaken. Prove balance and compiler inactive-column invariants. Local SIMD comparison does not remove aggregate guard.')
add('N5',h,'if state_only_copy_helper_sum(&h1)',['b482c','b4836','a4b85','a4b8f','a4b99','a4ba3','a4bb1'],'secret-derived helper total/Option guards',['V357','V360','V373'],'Expected constant when reached after successful nonpole helper: Some(0), no semantic error; b482c/b4836 false, owner JNE false and final JE true. Native helperSum plus padding/copy-balance association remains P.')
add('N6',s,'if state_only_boundary_sum',['c2bf0','c2bfe','c2c0c','c2c1a','c3122'],'secret-derived boundary/terminal equality guards',['V357','V360','V373'],'Expected constant on valid honest reached sumcheck: boundary equality all JNE false; terminal JE true. Requires native relation/degree/interpolation/oracle correspondence; not proved here.')
add('N7','tools/r1-cost-probe/src/bin/devnet_spend.rs','let keys:Vec<Keypair>',['8bf0c','8bf22','8bf4e','8bf99','8bf9e','8bf86','8df20','8dee1','8df96'],'secret byte decimal digit/zero control and cursor-dependent addresses',['V360','V373','V396'],'Not constant on valid decimal key arrays: secret seed bytes 0..31 have widths 1..3. Remaining 32 public-key bytes also parsed. Prove/storage observer binding remains P. Prove action has no JSON private witness fields; note selects deterministic fixture.')
add('N8','crates/aspis-r1-cost-probe/src/host_commitment.rs','fn validate_zero_tail',['bab92','baba1','babb0','babc5'],'secret-derived extension-tail guards before public lane partition',['V359','V360','V373'],'Expected constant on valid base/secure messages: excluded higher limbs zero; needs native domain proof; CT feature retains early guard branches.')
add('R1',e,'pub fn generate()',['13cdce','13cde7','13ce00','13cd03','13cd14','13cd63'],'96-byte zero rejection plus OS-status/partial-fill branches',['V352','V373','V371'],'96-byte route, including random nonce-zero guard; independent entropy/retry/environment and public failure witness-independence remain P. generate_for_mask_nonce not linked.')
add('R4','crates/aspis-core/src/field.rs','pub fn inv(self)',['199fd2','19b338'],'secret-derived inverse zero guard',['V373','V380-inversion','V371'],'M31 inverse public interpolation denominator versus secret/challenge helper denominator; source containment/nonpole/native zero boundary remains P.')
# Static branch-path accounting for valid unsigned integer tokens followed by comma or ].
initial=['8bef3','8bf0c','8bf4e','8bf5d'];ending=['8bfdd','8bfe7','8bff0','8bff5','8c01e'];paths={}
for d in [1,2,3]:
 path=initial+sum((['8bf99','8bf9e','8bf86'] for _ in range(d-1)),[])+['8bf99']+ending
 assert len(path)==3*d+7 and all(pcs[x]['op'].startswith('j') for x in path)
 paths[str(d)]={'digit_count':d,'Jcc_executions_in_parse_integer':len(path),'PC_sequence':path,'digit_range_exit_outcomes':['not taken']*(d-1)+['taken'],'overflow_guard_outcome':'8bf9e taken for each additional valid u8 digit; no overflow path'}
zero=['8bef3','8bf0c','8bf11','8bf22','8c0ec','8c0f1','8c0f6'];assert all(pcs[x]['op'].startswith('j') for x in zero)
paths['zero']={'Jcc_executions_in_parse_integer':len(zero),'PC_sequence':zero,'note':'zero special case; next digit is rejected as noncanonical JSON'}
(O/'N7-static-paths.json').write_text(json.dumps(dict(kind='manual symbolic path accounting checked against actual disassembly; not measured timing or dynamic trace',assumptions='valid unsigned decimal byte, no whitespace inside token, comma or ] delimiter present; excludes SeqAccess and Keypair validation',paths=paths,instructions=instructions(sorted(set(zero+sum([x['PC_sequence'] for k,x in paths.items() if k!='zero'],[]))))),indent=2)+'\n')
(O/'findings.json').write_text(json.dumps(dict(label=rec['label'],binary_sha256=rec['binary_sha256'],findings=findings),indent=2)+'\n')
# Grouped native inventory with reviewed family scope, never a transitive taint verdict.
families=[
 ('entropy/mask source',['state_only_entropy::','state_only_hiding::SeedExpander','state_only_hiding::sample_mask','state_only_hiding::derive_state_only'],'V352/V353/V354/V373/V371','R1/R2/R5 rejection/zero/refill/cursor history, public layout/reservation and fixed seed hashing; no provider timing proof'),
 ('mask application/balance',['state_only_hiding::apply_','state_only_hiding::balance_','prover::audit_masks'],'V354/V360/V373/V371','public geometry addresses and fixed arithmetic under descriptor provenance; N2/N4 private guards'),
 ('semantic/helper/sumcheck',['host_semantic::','host_sumcheck::','build_copy_logup_helper','compress_tagged_tuple','terminal_qm31','state_only_selected_mask_value','ct_pole::'],'V357/V360/V373/V380-inversion/V371','N1/N3/N5/N6; tuple slots indexed by public registry; challenge-point selector pruning retains joint-law P; field operands secret'),
 ('commit/encode/open',['host_commitment::','host_tree::','prover::fold','prover::round','prover::prove_from_semantics','prover::append_opening'],'V359/V360/V373/V371','N8 field-domain guards; fixed public lane/shape/round geometry; query addresses challenge-dependent; private salt/hash data'),
 ('hash/sign',['aspis_prover::host_hashv','sha2::','poseidon2::','curve25519_dalek::','ed25519_dalek::'],'V359/V360/V373/V396/V371','reviewed compression/table-selection bodies only: fixed/public schedule and addresses; contents arithmetic operands; CPU latency P'),
 ('public challenge/check',['aspis_z4b_probe::','aspis_r1_cert_','sampler::','QueryScan','query_scan'],'V356/V358/V360/V361/V362/V363/V364/V373/V371','raw FS history/certificate-dependent control and addresses; accepted transcript alone insufficient for joint rejected-prefix law'),
 ('entry/parser/compiler',['devnet_spend::','serde_json::','CopyRecords::','two_outputs','compile_pool_v1_pair_forest'],'V360/V373/V396/V371','entry uses fixture note/public JSON; N7 on separate signing route; honest compiler validity and full-client observer remain P')]
coverage=[]
for name,patterns,rows,classification in families:
 members=[{k:r[k] for k in ['symbol','start','end','direct_reachable','branches','division','indirect']} for r in inv if any(p in r['symbol'] for p in patterns)]
 coverage.append(dict(family=name,rows=rows,classification=classification,members=members,limit='family/provenance review; generic inline/allocator/dependency/OS closure not exhaustively taint verified'))
(O/'kernel-review.json').write_text(json.dumps(coverage,indent=1)+'\n')
# Focused branch contexts for crypto and referenced helpers, and every selected DIV.
summary=[]
for r in inv:
 if any(x in r['symbol'] for x in ['host_hashv','sha2::','poseidon2::','LookupTable<T>::select','SeedExpander::qm31','Profile21SourceExpander::qm31','QueryScan','sampler::','balance_qm31','from_le_bytes']):
  b=blocks[r['symbol']]['instructions'];wanted=set()
  for i,x in enumerate(b):
   if x['op'].startswith('j') or x['op'] in ['call','div','idiv']:
    wanted.update(range(max(0,i-2),min(len(b),i+2)))
  summary.append(r['symbol']+' '+r['start']+'..'+r['end']+'\n'+'\n'.join(str(b[i]) for i in sorted(wanted)))
(O/'branch-contexts.txt').write_text('\n\n'.join(summary)+'\n')
(O/'division.json').write_text(json.dumps([{'symbol':r['symbol'],'direct_reachable':r['direct_reachable'],'division':r['division']} for r in inv if r['division']],indent=2)+'\n')
# Configured fixture APIs versus linked executable, all main edges checked.
fixture_patterns=['deterministic_spend_fixture','v7_pair_forest_fixture','r0_fixture','build_hiding_atomic_state_only_spend_proof_v3','prove_masked_fixture','fixture_secret','tail_samples','test_hooks']
linked=[s for s in (O/'symbols.txt').read_text().splitlines() if any(p in s for p in fixture_patterns)];edges=[c for c in calls if c.get('callee') and any(p in c['callee'] for p in fixture_patterns)];assert not linked and not edges
(O/'fixture-review.json').write_text(json.dumps(dict(feature_enabled=True,patterns=fixture_patterns,linked_symbols=linked,resolved_call_edges=edges,source_call_review='main -> plan::run/prove -> prove_masked_retrying -> generate -> prove_masked_attempt; HashFn from HOST_HASH. No gated fixture constructor/callback in this source route. Local plan::note/digest ARE reachable deterministic fixtures, not gated aspis-prover APIs.',limits='Symbol absence alone cannot exclude arbitrary inlined code; source call route review supplies that association. No whole production-entropy claim.'),indent=2)+'\n')
# Capture relevant dependency sources, not keys, from the exact offline registry.
registry=Path('/home/dombarker/.cargo/registry/src');deps={}
for glob,filename,lo,hi in [('serde_json-1.0.151','src/de.rs',450,530),('solana-keypair-3.1.2','src/lib.rs',1,250)]:
 path=next(registry.glob('*/'+glob+'/'+filename));text=path.read_text();deps[glob]={'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'excerpt_first_line':lo,'excerpt':text.splitlines()[lo-1:hi]}
(O/'dependency-source.json').write_text(json.dumps(deps,indent=2)+'\n')
features=json.loads((O/'features.json').read_text());selected=[r for r in features if r['name'] in ['aspis-core','aspis-prover','aspis-r1-cost-probe','aspis-r1-cu-probe','aspis-r1-cert-build','aspis-r1-cert-check']];assert all('ct-host-prover' in r['features'] for r in selected if r['name'] in ['aspis-core','aspis-prover','aspis-r1-cost-probe']);assert all('optimized-terminal' not in r['features'] for r in selected)
(O/'selected-features.json').write_text(json.dumps(selected,indent=2)+'\n')
review=dict(target='manual PC/source bindings, static digit paths, grouped kernel inventory, fixture and resolved feature audit',source_revision=rec['source_revision'],binary_sha256=rec['binary_sha256'],exit_status=0,wall_seconds=time.monotonic()-t,limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']},cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),cgroup_swap_peak_bytes=int((cg/'memory.swap.peak').read_text()),print_axioms='N/A (no Lean)')
(O/'review-receipt.json').write_text(json.dumps(review,indent=2)+'\n');print(json.dumps(review))
