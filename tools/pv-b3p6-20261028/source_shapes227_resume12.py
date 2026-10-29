"""Mechanical whole-source shape checks for the newly bound model transforms.
The named Lean laws do the transformation work; this script does not interpret
Rust, certify dependency bodies, or turn a model law into a callback theorem.
"""
from pathlib import Path
import re,json,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');O=D/'resume12';P=Path('tools/pv-b3p6-20261028/v244')
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
def body(s,name):
 a=re.search(r'\bfn '+name+r'\b',s).start();b=s.index('{',a);i=b+1;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
lex=re.compile(r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\w+|[^\s]')
def tokens(s):return [m[0]for m in lex.finditer(s)if not m[0].startswith(('//','/*'))]
for n in ['host_terminal.rs','host_copy_terminal.rs']:
 assert (P/n).read_bytes()==Path('crates/aspis-r1-cost-probe/src',n).read_bytes(),n
rows=[]
def record(name,family,src,owned,expected,laws,remaining):
 assert tokens(expected)==tokens(owned),name
 rows.append(dict(body=name,family=family,source_sha256=sha(src),owned_sha256=sha(owned),normalized_sha256=sha('\0'.join(tokens(expected))),complete_function_shape_check=True,named_model_laws=laws,remaining=remaining,credit='checked source transformation shape and named model binding; NOT a fully composed own-1 association'))
s=body((P/'host_terminal.rs').read_text(),'add_preweighted');r=body((P/'reference_terminal.rs').read_text(),'add_preweighted')
old='for group in first..=last {';new='let mut group_index = first; while group_index <= last { let group=group_index; group_index+=1;'
assert s.count(old)==1
record('add_preweighted','terminal',s,r,s.replace(old,new),[
 'PV_B3P_Binding12227.preweighted_operation_binding12',
 'PV_B3P_Binding12227.preweighted_macro_step_binding12',
 'PV_B3P_Binding12227.source_four_loop_binding12',
 'PV_B3P_Binding12227.inclusive_loop_fold12'],
 ['apply iterator/source-library association including termination/drop at actual caller bounds','full dependency source binding'])
s=body((P/'host_copy_terminal.rs').read_text(),'active_literal');r=body((P/'reference_copy_terminal.rs').read_text(),'active_literal')
old='''let mask = constants::ACTIVE_ROW_MASKS[block];
            if mask != 0 {
                sum = sum.add(self.high[block].mul(selector_mask_sum_16(&self.low, mask)));
            }'''
assert s.count(old)==1
record('active_literal','copy',s,r,s.replace(old,'sum=active_block227(*self,block,sum);'),[
 'PV_B3P_Binding11227.active_block_source_binding11',
 'PV_B3P_Binding12227.active_literal_fold12'],
 ['complete binding of frozen-mask implementation and source/library operations, preserving all observation obligations'])
s=body((P/'host_copy_terminal.rs').read_text(),'pattern_values_literal');r=body((P/'reference_copy_terminal.rs').read_text(),'pattern_values_literal')
a=s.index('if pattern.kinds[limb] == 1 {');j=s.index('{',a)+1;depth=1
while depth:depth+=(s[j]=='{')-(s[j]=='}');j+=1
expected=s[:a]+'value = pattern_limb227(pattern,limb,*openings,powers,value);'+s[j:]
record('pattern_values_literal','copy',s,r,expected,[
 'PV_B3P_Binding12227.pattern_step_binding12',
 'PV_B3P_Binding12227.pattern_loop_binding12',
 'PV_B3P_Binding12227.pattern_outer_binding12',
 'PV_B3P_Binding12227.pattern_values_literal_binding12'],
 ['actual borrowed/owned copy and source-library association for the complete caller'])
x=dict(rows=rows,features='native227-composition-features.json; expanded pinned-compiler bodies in resume12',boundary='V370 / pending owner D381,D386 retained',semantic_use='reclassification within existing Charon/Aeneas tool trust',fully_composed_own_1_credit=0)
p=O/'source-shape-checks.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==x
else:p.write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(whole_function_shape_checks=len(rows),fully_composed_own_1_credit=0)))
