"""Prepare strict row packets; no admission is performed by this generator."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent
old=json.loads((E/'NHU_CLOSED.json').read_text());mark=old['functions'][0]
core='crates/aspis-core/src/state_only_hiding.rs::';terminal='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::';poseidon='crates/aspis-statement/src/state_only_poseidon.rs::'
spec=[
 (71,core+'cm31_mul_i','AspisR1.NHU_MaskHelpers.cm_i',[(31,32)],'SAME canonical CM31 receiver, both raw limbs<2147483647; all such values including zero','immutable helper: actual frozen proof_for_contract against safe conditional-negation record reference; empty modifies'),
 (73,core+'mask_power_26','AspisR1.NHU_Power.result',[(10,11)],'SAME canonical QM31 receiver including zero; every emitted intermediate canonical by NHU_Power.domains','exact six-call native source cut; complete emitted power26 packet; local opaque square/product records'),
 (74,core+'mul_tower_basis','AspisR1.NHU_Tower.result',[(35,36)],'SAME canonical QM31 receiver, coordinate<4; four branch reference table NHU_TowerPacket.table','immutable helper: actual frozen proof_for_contract against safe four-branch record reference; empty modifies'),
 (75,core+'selected_mask_linears','AspisR1.NHU_Linears.result',[(12,13),(14,15)],'SAME point10, every coordinate canonical; arbitrary reverse-loop canonical prestate and preserved suffix/weighted invariants','one actual reverse iteration, scalar-call suffix and retained ten-step emitted induction'),
 (76,core+'state_only_selected_mask_value','AspisR1.NHU_Mask.result',[(16,17),(18,19),(20,21),(22,23),(24,25),(26,27)],'SAME c1[16], maskOnly[10], g and point[10], every value canonical; zero allowed; actual prepared constructor and seeded coefficient/Horner domains','frozen native opening/coefficients/setup/Horner/final cuts, exact local records and frames; total complete emitted/adopted packet'),
 (230,terminal+'add_preweighted','AspisR1.NHU_Preweighted.result',[(45,46),(47,48),(49,50),(51,52)],'deployed N in {2,12,16,17}; 0<N, start+N<=96; SAME canonical packed24 and values[N]; actual active or exhausted RangeInclusive invariant','one actual arbitrary-prestate group iteration per fixed array ABI, exact argument/reply/frame/cursor laws plus total emitted induction'),
 (243,terminal+'lift_m31','AspisR1.NHU_Lift.result',[(37,38)],'every raw u32, including noncanonical words; no arithmetic precondition','immutable helper: actual frozen proof_for_contract against safe fixed record constructor reference; empty modifies'),
 (248,terminal+'poseidon_selectors','AspisR1.NHU_PoseidonSelectors.result',[(55,56)],'SAME selectors; high64 and low16 canonical; exact single range0..57, returned local is SAME low16','native frozen record constructor with closed sum_high local call record; total emitted SAME-owner/range packet'),
 (322,poseidon+'interpolate_three_constant_limb','AspisR1.NHU_Interpolation.result',[(68,69)],'SAME six raw input words, each<2147483647; natural widened products and sum bounded by3*4611686009837453316<2^64','exact frozen product/reducer local records; native bounded u64 additions; total emitted natural product/sum/modulo laws'),
 (326,poseidon+'pow5','AspisR1.NHU_Pow5.result',[(60,61)],'SAME canonical QM31 receiver including zero; every square/fourth/product domain proved by NHU_Pow5.domains','exact frozen square/square/mul local records; total emitted exponent5 packet')]
rows=[]
for n,fun,root,pairs,domain,form in spec:
 rows.append(dict(function=fun,rows=[f'TX1:{n:03}'],status='CLOSED',form=form,domain=domain,lean_root=root,native_pairs=[[f'NHU_K{a:03}',f'NHU_K{b:03}'] for a,b in pairs],modifies='only declared LOCAL call records and LOCAL output windows; immutable caller inputs; no external state, callback, digest, profiling or allocation event',inner_hypotheses_remaining=[],trust='P6/D188 option-A semantic transport RECLASSIFICATION, never removal; compiler/ABI/Std/SDK/Aeneas/source-to-ELF retained; no new trust'))
next(r for r in rows if r['rows']==['TX1:230'])['modifies']='packed current-group output cell only on an active iteration; every other packed cell unchanged; values/start and enclosing caller state immutable; local record/cursor only'
rows.append(mark);rows.sort(key=lambda r:r['rows'][0]);out=dict(frozen_revision=old['frozen_revision'],functions=rows,headline='AspisR1.RPx_Deployed.deployed',root137_closed=False,finish136_closed=False,prepare_op9_instantiated=False)
(E/'NHU_CANDIDATE.json').write_text(json.dumps(out,indent=1)+'\n');print(len(rows))
