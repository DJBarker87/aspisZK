"""Generate six pattern families, never 528 ad hoc proof obligations.

Every inventory event is assigned exactly once. A family application stays
CONDITIONAL until its actual-source state/guard certificate is supplied. A
successful compile is not evidence for that missing source certificate.
"""
from pathlib import Path
import json,hashlib,collections,argparse
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18'
parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
p=R/'FORMATTING-EVENTS-D569.json';inventory=json.loads(p.read_text());groups=collections.defaultdict(list)
for e in inventory['events']:
 c=e['category'];d=e['detail']
 if c.startswith('builtin index'):
  pattern='slice_range' if d['builtin']['Index']['is_range'] else 'index_out_of_bounds'
  guard=dict(kind='index_lt_length',operands=d['arguments'],length='const generic for array; actual backing length for slice')
 elif c=='MIR assertion':
  pattern='assertion';guard=dict(kind='condition_eq_expected',condition=d['assert']['cond'],expected=d['assert']['expected'],on_failure=d['on_failure'])
 elif c=='direct panic':
  pattern='assertion' if 'assert_failed' in str(d) else 'explicit_panic'
  guard=dict(kind='avoid_source_abort_arm',branch_path=e['lexical_branch_path'])
 else:
  n=d['name']
  if 'get_unchecked' in n:pattern='index_out_of_bounds';guard=dict(kind='index_lt_length',operands=d['arguments'])
  elif 'unchecked_add' in n or 'unchecked_sub' in n:
   pattern='arithmetic_overflow';guard=dict(kind='sum_le_usize_max' if 'unchecked_add' in n else 'rhs_le_lhs',operands=d['arguments'])
  elif 'expect_failed' in n:pattern='unwrap_expect';guard=dict(kind='upstream_option_isSome',branch_path=e['lexical_branch_path'])
  elif 'assert_unchecked' in n:pattern='assertion';guard=dict(kind='condition_true',operands=d['arguments'])
  elif '::fmt::' in n or 'panic_nounwind_fmt' in n:
   pattern='explicit_panic';guard=dict(kind='exclude_incoming_diagnostic_cone',branch_path=e['lexical_branch_path'],note='forwarding helper may have no local avoiding branch; incoming reachability must be proved')
  else:raise AssertionError(n)
 groups[pattern].append(dict(instance=e['instance'],statement=e['statement'],category=c,span=e['span'],guard=guard,local_control_law=e.get('local_control_law'),lemma='PV_B3P_PanicPatterns571227.'+pattern,source_state_binding='OPEN',actual_reachable_guard_proof='OPEN'))
patterns=['index_out_of_bounds','slice_range','arithmetic_overflow','unwrap_expect','explicit_panic','assertion']
counts={k:len(groups[k])for k in patterns};assert sum(counts.values())==528
assert counts==dict(index_out_of_bounds=468,slice_range=0,arithmetic_overflow=19,unwrap_expect=3,explicit_panic=7,assertion=31),counts
# Family carrier and arity are fixed by the pattern. State, actual reachability
# and guard validity are deliberately *not* synthesized from inventory metadata.
shape={
 'index_out_of_bounds':('IndexState','indexGuard','state site'),
 'slice_range':('SliceState','sliceGuard','state site'),
 'arithmetic_overflow':('ArithmeticState','arithmeticGuard','state site'),
 'unwrap_expect':('Option Unit','optionGuard','state site'),
 'explicit_panic':('Bool','fun b => b = true','state site'),
 'assertion':('Bool × Bool','fun b : Bool × Bool => b.1 = b.2','(state site).1 (state site).2')}
s='import PV_B3P_PanicPatterns571227\nnamespace PV_B3P_PatternFamilies571227\nopen Aeneas Aeneas.Std PV_B3P_PanicPatterns571227\nset_option autoImplicit false\n'
for pattern in patterns:
 n=counts[pattern]
 if n==0:continue # No vacuous slice-range family is promoted to a source law.
 typ,guard,operands=shape[pattern]
 s+=f'''/-- {n} inventoried sites. CONDITIONAL: source-state and guard links OPEN. -/
theorem {pattern}_family {{α State : Type}} (state : Fin {n} → State → {typ})
    (actual : Fin {n} → State → Prop)
    (guards : ∀ site s, actual site s → ({guard}) (state site s))
    (normal first second : Result α) :
    ∀ site s, actual site s →
      ¬ diagnostic (({guard}) (state site s)) ∧
      branch (({guard}) (state site s)) normal first =
        branch (({guard}) (state site s)) normal second := by
  intro site s reached
  exact ({pattern} {operands.replace('state site','state site s')} normal first second).2 (guards site s reached)
#print axioms {pattern}_family
'''
s+='end PV_B3P_PatternFamilies571227\n'
# Assertion direct-abort row requires its upstream condition to be supplied;
# this is intentionally not treated as an extracted assert equation.
meta=dict(inventory_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),counts=counts,groups=dict(groups),source_certificate_complete=False,formatting_unreachability_complete=False,guard_certificates_added_to_endpoint=False,premises_removed=[],premises_added=[],qualification='Grouping and generic lemma application only. Actual source-state binding and reachable guard proofs remain explicit; opaque helper interiors are not contained in the 528 available-body inventory.',generated_module_sha256=hashlib.sha256(s.encode()).hexdigest())
outputs={D/'lean/PV_B3P_PatternFamilies571227.lean':s,R/'PANIC-PATTERN-GROUPS-D571.json':json.dumps(meta,indent=2)+'\n'}
for p,t in outputs.items():
 if args.check:assert p.read_text()==t,p
 else:p.write_text(t)
print(json.dumps(dict(counts=counts,generated_families=5,actual_source_certificate=False,check=args.check)))
