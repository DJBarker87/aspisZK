from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3q-20261029');B=Path('evidence/pv-b3p6-20261028');x=json.loads((D/'d188-inventory.json').read_text())
old9=json.loads((B/'fidelity227-comparison-resume5.json').read_text());assert old9['all_equal'] and old9['cases']==36
old4=json.loads((B/'resume13/d18813-expected.json').read_text());assert len(old4)==16
native=json.loads((D/'host/d188-positive-comparison.json').read_text());assert native['actual_rows']==native['expected_rows']==96 and not native['mismatches']
new_names=['absorption_lanes_literal','path_lanes_literal','add_value_lanes','occupancy_lanes_literal','external_linear_packed','internal_sum227','leading_pair_packed','interpolate_three_constant_columns','expand','accumulate_endpoint','semantic_initial','host_terminal_field_pack','reference_field_pack','select227','mask_fragment']
rows=[]
for r in x['functions']:
 name=r['function'];group=name.rsplit('.',1)[-1]
 if '.Selectors.expand' in name:family='expand'
 elif '.pattern_values_literal_loop' in name:family='pattern_values_literal'
 elif '.add_preweighted_loop' in name:family='add_preweighted'
 elif '.composition_parts_loop' in name:family='mask_fragment'
 elif '.select227_loop' in name:family='select227'
 elif name.startswith('host_terminal_field.qm31_pack'):family='host_terminal_field_pack'
 elif name.startswith('reference_field.qm31_pack'):family='reference_field_pack'
 elif group=='accumulate_prepared227':family='qm31_sum_products3_prepared'
 elif group=='semantic_initial_and_absorption':family='semantic_initial'
 else:family=group
 if family in old9['functions']:kind='inherited 36 comparisons';path=str(B/'fidelity227-comparison-resume5.json')
 elif family in {v['function']for v in old4}:kind='inherited 16 comparisons';path=str(B/'resume13/d18813-expected.json')
 else:
  assert family in new_names,(name,family)
  kind='new 96 comparisons';path=str(D/'host/d188-positive-comparison.json')
 assert not r['review']
 rows.append(dict(function=name,family=family,module=r['module'],source_sha256=r['source_sha256'],body_sha256=r['body_sha256'],mutable_borrows=len(r['mutable_borrows']),direct_updates=len(r['direct_updates']),restoration_review='all back functions applied; every stored state consumed',finite_comparison=kind,comparison=path,existing_links=['PV_B3P_Groups14227.PV_B3P_Link_D188','PV_B3P_Binding14227.PV_B3P_Link_matrix_stores'if'prepared'in name else'PV_B3P_Groups14227.PV_B3P_Link_std_dependency_closure14'],status='per-function D188 restoration inspection and executable comparison present; not universal changed-function native association'))
out=dict(scope='all 29 generated mutating declarations in accepted root closure (27 Rust function families after loop grouping)',declarations=len(rows),mutable_borrow_sites=x['mutable_borrow_sites'],direct_update_sites=x['direct_update_sites'],flagged=0,new_comparisons=96,reused_comparisons=52,rows=rows,source_association_limit='source-body fidelity, alias/caller binding and full dependency closure remain their separately named obligations',compiler_boundary='V370 / pending D381,D386 retained')
(D/'d188-function-status.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='rows'}))
