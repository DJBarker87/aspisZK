"""Record the exact structural source association and its explicit native limits."""
from pathlib import Path
import json,hashlib,subprocess,re
E=Path('evidence/pv-batch2-20261027/batch2f');L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();rows=[]
paths=['crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/host_weights.rs','crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-r1-cost-probe/src/prover_powers.rs','crates/aspis-r1-cost-probe/src/transport.rs','crates/aspis-core/src/r0/heap.rs','crates/aspis-core/src/r0/opening.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/ct.rs']
for p in paths:
 b=Path(p).read_bytes();hb=subprocess.check_output(['git','show','HEAD:'+p]);assert b==hb
 rows.append(dict(path=p,git_blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip(),sha256=hashlib.sha256(b).hexdigest()))
proofs=json.loads((E/'ACCEPTED-PROGRESS.json').read_text())['sources']
for a in proofs:
 if '/PV_B2_F_' not in a['module']:continue
 p=Path(a['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==a['source_sha256']
 a['worktree_git_blob']=subprocess.check_output(['git','hash-object',str(p)],text=True).strip()
assoc=[
 ('weights::powers::<7> versus prover_powers::<7>','same ordered seven powers, no final unused multiply; batch1 shared op254 credit is reused once; copied powers totality and adapter are checked','PV_B2_C_Powers7Total.source'),
 ('pure powers before allocation versus after allocation','unconditional powers totality transports the prefix across every request Result, including outer fail/div','PV_B2_F_MaterializeRequest.after_eq_before'),
 ('both caller paths request heap::filled(1024,E::ZERO)','heap implementation uses try_reserve_exact then resize; same request size/value and maps reservation error to Error::Allocation; every modeled request outcome is quantified, never assumed successful','PV_B2_F_AllocationEffects.complete_result'),
 ('original enumerate+iter_mut and inner kind0..6','same ordered seven contributions; original reads current zero slot and restores each mutable write; suffix invariant proves untouched cells stay zero','PV_B2_F_OriginalMutation.loop'),
 ('copy direct indexed updates','loop forwards the Array.update result and returns full mutable state; no discarded restoration, no whole1024-cell kernel reduction','PV_B2_F_MutationModel.source'),
 ('frozen raw match, kind0 inactive guard, kind4 power, D point and tensor folds','all Usize indices and every branch/error; explicit inactive guard is proved safe on every returned row; invalid D reads fail before that guard','PV_B2_F_RawGuard.source'),
 ('QM31 canonicalization and WideExact mixed product','selected ct-host-prover branch reduces four raw RHS limbs with the exact ct reducer; mixed product matches the direct two-quartic field construction; from_limbs/unwrap succeeds by symbolic canonicality','PV_B2_D_MulQm31Total.source'),
 ('native carrier and complete output','all eleven error variants are mapped separately; both field coordinates and every vector cell are retained; exact op25 weights carrier and259 unselected callbacks preserved','PV_B2_F_MaterializeNative.callbacks'),
 ('frozen source call order and complete callback','original ordered mutable semantics, powers before the fallible request, all error/divergence cases, no success/canonicality/source-equality premise','PV_B2_F_251Bridge.source')]
j=dict(operation=251,representation='PV_B2_F_MaterializeRequest.original',source_revision=rev,inputs=rows,proof_sources=proofs,source_correspondence=[dict(rust=r,association=a,theorem=t) for r,a,t in assoc],native_link_evidence_class='Reviewed structural source/caller argument plus universal Lean Result equality for every allocation-request context and exact selected native-carrier installation; not fresh Aeneas extraction of the original mutable iterator and not a native execution/OS proof',native_fidelity='../batch2c/D188-FULL-COMPARISON.json; complete1024-cell results and changing outputs for S1/S2/D; unchanged materialize/raw/powers source bodies',scope='Selected candidate source/callback row only; the request is universally quantified, not a new trust item or success premise. Actual native RunJoin installation, OS-failure witness independence and L1/L2/L3 remain P obligations.',no_mutable_iterator_borrow_in_copy=True,no_XR=True,trust_fields=['entropy_law','entropy_kernel','observation'],focused_closure=40837)
(E/'MATERIALIZE-STRUCTURAL-BINDING.json').write_text(json.dumps(j,indent=2)+'\n')
r=json.loads((E/'40837.json').read_text());ss=[]
for f in ['PV_B2_F_MaterializeRequest.lean','PV_B2_F_251Bridge.lean','PV_B2_F_251Closure.lean']:
 s=(L/f).read_text()
 for m in re.finditer(r'^theorem \w+.*?(?=^theorem |^def |^#print |^end |\Z)',s,re.M|re.S):ss.append(dict(source=str(L/f),statement=m.group(0).split(':=')[0].strip()))
row=dict(row='V258',operation=251,status='CLOSED_SELECTED_ALLOCATION_CONTEXT_SOURCE_CALLBACK',closing_theorems=['PV_B2_F_MaterializeRequest.complete_result','PV_B2_F_251Bridge.source','PV_B2_F_251Closure.three_rows'],statements=ss,ambient_context='Every base ExternalTypes; op25 instantiated to the exact four-field weights structure. Every request : Result Outcome, ops in that carrier, weight and native kappa. No success/canonicality/source-equality premise.',nonvacuity='All weights/kappas succeed for ok supplied. ok denied yields exactly native Error::Allocation; fail e and div are preserved. Source kernel success is unconditional. This does not assert every native allocation succeeds.',native_link_evidence_class=j['native_link_evidence_class'],native_limits=j['scope'],binding='MATERIALIZE-STRUCTURAL-BINDING.json',receipt={k:r[k] for k in ['attempt','module','source_revision','source_sha256','exit_status','wall_seconds','peak_rss_kib','swaps','accepted_axioms']},print_axioms='40837-stdout.log')
(E/'V258.json').write_text(json.dumps(row,indent=2)+'\n');(E/'V258.md').write_text('# V258 / op251\n\n'+row['status']+'\n\n'+row['ambient_context']+'\n\n'+row['nonvacuity']+'\n\n'+j['native_link_evidence_class']+'\n\n'+j['scope']+'\n\n'+''.join('```lean\n'+x['statement']+'\n```\n\n' for x in ss))
print('recorded allocation-context source association and exact V258 statements')
