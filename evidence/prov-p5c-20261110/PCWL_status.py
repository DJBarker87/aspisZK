import json,re,glob,subprocess
tri=json.load(open('PCWL_TRIAGE.json'))
STD={'propext','Classical.choice','Quot.sound'}
def rc(s):
    r=json.load(open(s+'/receipt.json'))
    ax=[];bad=[]
    for x in r['print_axioms']:
        if 'does not depend' in x: continue
        m=re.search(r'axioms: \[(.*)\]',x,re.S);a={y.strip() for y in m.group(1).split(',')} if m else {'?'}
        ax.append(sorted(a))
        if not a<=STD: bad.append(x[:120])
    return dict(scope=s,exit=r['exit_status'],wall_s=round(r['wall_seconds'],1),peak_rss_gib=round(int(r['peak_rss_kib'])/1048576,2),swap=r['swaps'],n_print_axioms=len(r['print_axioms']),nonstandard=bad,source_revision=r.get('source_revision'),caps='MemoryHigh=6G MemoryMax=8G MemorySwapMax=0, lean -M7000')
SC={s:rc(s) for s in ['PCWL_L001','PCWL_L006','PCWL_L009','PCWL_L012','PCWL_L014','PCWL_L015','PCWL_L027']}
def decls(f): return set(re.findall(r'(?m)^(?:theorem|def) (PRVEq\.\S+)',open(f).read()))
def find(f,ML,suffix):
    d=decls(f)
    for cand in (f'PRVEq.{ML}.{suffix}.equiv',f'PRVEq.{ML}.{suffix}'):
        if cand in d: return cand
    return None
rows=[]
def add(mod,defn,status,**kw):
    rows.append(dict(module=mod,definition=defn,status=status,**kw))
# AspisR1AdapterReconstruct.Types
f='PRVEq_AspisR1AdapterReconstruct_Types_w1.lean'
for r in tri['modules']['AspisR1AdapterReconstruct.Types']['definitions']:
    suf=r['definition'].split('AspisR1AdapterReconstruct.',1)[1]
    th=find(f,'AspisR1AdapterReconstruct.Types_w1',suf)
    add('AspisR1AdapterReconstruct.Types',r['definition'],'EQUALITY_PROVED' if th else 'OPEN',theorem=th,file=f,scope='PCWL_L001',configuration='ON (types: declaration text independent of overflow checks)',kind='type isomorphism (Equiv fresh gate)',emission='evidence/prov-p4e-20261109/PCWE_E003_emitted (original Aeneas 959659a6, ON, frozen 4bb3b3f; PINS PCWE_E003_PINS.json)')
# CurrentCompactCallerTypesV1
f='PRVEq_CurrentCompactCallerTypesV1_w2.lean'
for r in tri['modules']['CurrentCompactCallerTypesV1']['definitions']:
    suf=r['definition'].split('AspisR1CurrentCaller.',1)[1]
    th=find(f,'CurrentCompactCallerTypesV1_w2',suf)
    add('CurrentCompactCallerTypesV1',r['definition'],'EQUALITY_PROVED' if th else 'OPEN',theorem=th,file=f,scope='PCWL_L006',configuration='ON',kind='type isomorphism (Equiv fresh gate); closures: fresh = gate by rfl',emission='evidence/prov-p1j-20261110/PCVJ_E002_emitted (Aeneas b59d5188-extended, ON, frozen 4bb3b3f; PINS PCVJ_E002_PINS.json); not re-emitted with the original tool')
# CurrentClaimSumModel
f='PRVEq_CurrentClaimSumModel_w3.lean'
mp={'AspisR1CurrentPreparedClaim.aspis_core.field.WideExact':'aspis_core.field.wide_exact.WideExact','AspisR1CurrentPreparedClaim.r1_wire.Challenges':'aspis_core.state_only_prefix.r0.Challenges','AspisR1CurrentPreparedClaim.r1_semantic.Verified':'r1_semantic.Verified','AspisR1CurrentPreparedClaim.r1_wire.SemanticTranscript':'r1_wire.SemanticTranscript','AspisR1CurrentPreparedClaim.verifier.Error':'verifier.Error'}
for r in tri['modules']['CurrentClaimSumModel']['definitions']:
    d=r['definition']
    if d in mp:
        th=find(f,'CurrentClaimSumModel_w3',mp[d])
        add('CurrentClaimSumModel',d,'EQUALITY_PROVED' if th else 'OPEN',theorem=th,file=f,scope='PCWL_L014',configuration='ON',kind='type isomorphism with name map (crate path of WideExact and Challenges differs: encoding difference, fields identical)',emission='evidence/prov-p1j-20261110/PCVJ_E002_emitted (extended, ON, frozen)')
    elif d.endswith('WideExact.ZERO'):
        th=find('PRVEq_CurrentClaimSumModel_w6.lean','CurrentClaimSumModel_w6','field.wide_exact.WideExact.ZERO')
        add('CurrentClaimSumModel',d,'EQUALITY_PROVED' if th else 'OPEN',theorem=th,file='PRVEq_CurrentClaimSumModel_w6.lean',scope='PCWL_L015',configuration='ON (constant)',kind='fresh = gate (constant)',emission='evidence/prov-p1k-20261110/PCVR_E006_emitted (original Aeneas, ON, frozen 4bb3b3f)')
    else:
        add('CurrentClaimSumModel',d,'OPEN',cause='CANNOT_EXTRACT' if 'prepared_claim_sum' in d else 'GATE_ONLY_NAME',reason='frozen counterpart is verifier::prepared_claim (crates/aspis-r1-cost-probe/src/verifier.rs 53-70); PCWL_E006 (original Aeneas, roots prepared_claim, 9 opaque callees): "Returns inside of nested loops are not supported yet", body ignored; extended Aeneas crashes (Not_found in InterpReduceCollapse.collapse_ctx_following_sequence, PCWL_E003/E004 on the same loop-return class). The gate prepared_claim_sum* is a fission of that loop with no frozen function of that name.' if 'prepared_claim_sum' in d else 'gate closure of the fission function prepared_claim_dot; no frozen declaration of that name; the frozen closure type (prepared_claim::closure, map_err) is declared in the PCWL_E006 partial emission but equating it to the gate closure of a differently named function is not an encoding difference, so not counted')
# AdapterRw
A=tri['modules']['AdapterRwModel']['definitions']
for r in A:
    d=r['definition'];n=d.split('AdapterRw.',1)[1]
    if n.endswith('readonly_buffer_meta_ok') or n.endswith('owned.require_readonly_buffer'):
        th=find('PRVEq_AdapterRwModel_w4.lean','AdapterRwModel_w4',n)
        add('AdapterRwModel',d,'EQUALITY_PROVED' if th else 'OPEN',theorem=th,file='PRVEq_AdapterRwModel_w4.lean',scope='PCWL_L009',configuration='ON (no arithmetic in these bodies; ON and OFF emissions coincide)',kind='fresh = gate (function equality, rfl)',emission='PCWL_E001 (original Aeneas 959659a6, ON, frozen 4bb3b3f)')
    elif n.endswith('readonly_meta_ok') or n.endswith('owned.require_readonly_account'):
        th={'readonly_meta_ok':'PRVEq.AdapterRwModel_w5.readonly_meta_ok_eq','owned.require_readonly_account':'PRVEq.AdapterRwModel_w5.require_readonly_account_eq'}['readonly_meta_ok' if n.endswith('readonly_meta_ok') else 'owned.require_readonly_account']
        add('AdapterRwModel',d,'CONDITIONAL_ON_BINDING',theorem=th,file='PRVEq_AdapterRwModel_w5.lean',scope='PCWL_L012',configuration='ON',kind='fresh(Ext) = gate(ops) under x.pk_eq = ops.op36',binding='the fresh emission has Pubkey equality as an external axiom; the compiled gate takes it as ops.op36. The equality holds for every Ext with pk_eq = ops.op36. The binding itself (SDK Pubkey::eq = ops.op36) is HM-A / constant binding, not proved here.',emission='PCWL_E001')
    elif n.endswith('owned.require_zero'):
        add('AdapterRwModel',d,'EQUALITY_PROVED',theorem='PRVEq.AdapterRwModel_w7.require_zero_eq',file='PRVEq_AdapterRwModel_w7.lean',scope='PCWL_L027',configuration='ON (the frozen function has no arithmetic; the gate index loop uses wrapping_add on a bounded index)',kind='extensional fresh = gate for all inputs (loop simulation proof)',source_difference='gate loops by index (index < bytes.len(), wrapping_add), frozen loops over remaining = &remaining[1..]; values agree for all slices (proved), the source text differs',emission='PCWL_E001')
    elif n.endswith('require_zero_loop') or n.endswith('require_zero_loop.body'):
        add('AdapterRwModel',d,'GATE_ONLY_HELPER_CLEARED_THROUGH_PARENT',parent='AdapterRw.r1_pool_adapter.owned.require_zero',theorem='PRVEq.AdapterRwModel_w7.gate_loop (gate loop = pure spec gs for every index)',file='PRVEq_AdapterRwModel_w7.lean',scope='PCWL_L027',reason='the frozen function has a different loop state (slice) so there is no frozen counterpart of the gate loop or body; they are used only through the parent equality, and gate_loop characterises the gate loop completely')
    elif 'require_distinct_accounts' in n:
        add('AdapterRwModel',d,'OPEN',cause='CANNOT_EXTRACT',reason='frozen fn owned::require_distinct_accounts (r1_pool_adapter_owned.rs 59-72, nested while with `return Err`). PCWL_E001 original Aeneas 959659a6: "Returns inside of nested loops are not supported yet". PCWL_E002 (extended b59d5188 on the saved LLBC): exit 2, no message. PCWL_E003 (extended, full run with the roots): uncaught Not_found in InterpReduceCollapse.collapse_ctx_following_sequence. Shape class retired.',tool_route='Aeneas support for returns inside nested loops, or a fix of the extended-tool Not_found; a source refinement of the frozen function is a frozen-source change and was not made',config_note='the gate uses wrapping_add on the index (overflow OFF shape) while the frozen build here is ON; unresolved because no fresh text exists')
    elif 'authenticate_invariant_release_registry' in n:
        add('AdapterRwModel',d,'OPEN',cause='PARAMETRIC_OPS (not attempted)',reason='fresh emission exists (evidence/tx2-auth-20261111/NMX_registry_emitted, extended Aeneas, ON, frozen) with 28 external axioms (FunsExternal_Template). A statement needs an Ext record with those 28 fields typed in the gate namespace, the 880-line gate function and the fresh function copied with externals replaced by Ext fields, and one binding hypothesis per used ops field (the compiled gate numbers them differently from the repository source: Pubkey eq is op36, not op38). Not done within the budget; next deliverable.')
    else:
        add('AdapterRwModel',d,'OPEN',cause='UNCLASSIFIED')
# S1Claim modules
for m in ['S1ClaimBorrowedAbiNativeV1','S1ClaimOwnedNestedModelV1']:
    for r in tri['modules'][m]['definitions']:
        add(m,r['definition'],'OPEN',cause='CANNOT_EXTRACT / NO_FROZEN_COUNTERPART',reason='the gate owned_* / owned_claim_loops* functions are hand-restructured (ops : ClaimDotOps D record, fissioned loops with pending results, ownedIsErr) copies of the loop structure of frozen verifier::prepared_claim, which has no Aeneas extraction (PCWL_E006: nested-loop return unsupported; extended tool crashes). No frozen function of these names exists in 4bb3b3f. Owner-approved reconstruction (ReconstructedSource, not frozen-equal) was not attempted: it would not discharge frozen provenance and the nested return would hit the same Aeneas limit in the frozen function.',tool_route='extract verifier::prepared_claim once Aeneas supports returns in nested loops (or the extended-tool crash is fixed), then prove the fission/owned restructuring as a refinement of the extracted loops')
json.dump(dict(schema='PCWL_STATUS/1',target_established=False,statement='Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed; no trust row added; nothing pushed or merged.',frozen_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',branch='codex/pc-prov-p5c-20261110',budget=dict(lean_scopes_used=27,lean_scopes_max=35,extraction_scopes_used=6,extraction_scopes_max=10),scopes=SC,definitions=rows),open('PCWL_STATUS.json','w'),indent=1)
import collections
c=collections.Counter((r['module'],r['status']) for r in rows)
for k,v in sorted(c.items()): print(k,v)
print(sum(1 for r in rows if r['status']=='EQUALITY_PROVED' and not r.get('theorem')))
print([ (r['definition'],r['status']) for r in rows if r['status']=='OPEN' and r['module'] in('CurrentCompactCallerTypesV1','AspisR1AdapterReconstruct.Types')])
