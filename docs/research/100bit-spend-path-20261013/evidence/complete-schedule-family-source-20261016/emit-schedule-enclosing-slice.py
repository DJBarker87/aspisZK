from pathlib import Path
import hashlib,json,re
repo=Path('/Users/dominic/ZK/.worktrees/100bit-spend-path');p=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261016/Funs.lean';s=p.read_text();prefix='pool_v1.pair_forest_semantic_terminal.'
mapping={prefix+'sum_high':'AspisR1SumHighCandidate.'+prefix+'sum_high',prefix+'initial_variant_selectors':'AspisR1InitialVariantCandidate.'+prefix+'initial_variant_selectors',prefix+'absorption_lanes_literal':'AspisR1AbsorptionCandidate.'+prefix+'absorption_lanes_literal',prefix+'semantic_initial_and_absorption.closure':'AspisR1InitialCandidate.'+prefix+'semantic_initial_and_absorption.closure',prefix+'add_preweighted':'AspisR1PreweightedCandidate.'+prefix+'add_preweighted','poseidon2.RATE':'AspisR1InitialCandidate.poseidon2.RATE'}
for x in ['DOMAIN_OWNER_KEY','DOMAIN_NOTE','DOMAIN_NULLIFIER']:mapping['spend.'+x]='AspisR1ScheduleDomainCandidate.spend.'+x
pattern=re.compile('|'.join(re.escape(k) for k in sorted(mapping,key=len,reverse=True)));rev={v:k for k,v in mapping.items()};inverse=re.compile('|'.join(re.escape(v) for v in sorted(rev,key=len,reverse=True)));rows=[];blocks=[];sha=lambda b:hashlib.sha256(b).hexdigest()
for name in ['semantic_initial_and_absorption','add_schedule_lanes']:
 start=re.search(r'\bdef\s+'+re.escape(prefix+name)+r'(?=\s|:)',s).start();end=s.index('\n/-- ',start);body=s[start:end].rstrip()+'\n';adapted=pattern.sub(lambda m:mapping[m.group()],body);assert inverse.sub(lambda m:rev[m.group()],adapted)==body
 rows.append({'name':prefix+name,'start_byte':len(s[:start].encode()),'end_byte':len(s[:end].encode()),'raw_declaration_sha256':sha(body.encode()),'adapted_declaration_sha256':sha(adapted.encode()),'inverse_recovers_exact_declaration':True});blocks.append(adapted)
header='''import SumHighGeneratedSlice
import InitialVariantSlice
import InitialCallbackSlice
import AbsorptionGeneratedSlice
import ScheduleDomainConstants
import PreweightedLoopSlice

/-! Whole generated schedule array producer and enclosing packing caller.
Only helper-reference qualification and the namespace are adapted. The
inverse map recovers every original declaration byte. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1ScheduleEnclosingCandidate
open AspisR1SelectedMaskProbe

'''
q=Path('/tmp/ScheduleEnclosingSlice.lean');q.write_text(header+'\n'.join(blocks)+'\nend AspisR1ScheduleEnclosingCandidate\n')
Path('/tmp/ScheduleEnclosingSlice.manifest.json').write_text(json.dumps({'raw_generated_path':str(p.relative_to(repo)),'raw_generated_sha256':sha(p.read_bytes()),'declarations':rows,'module_sha256':sha(q.read_bytes()),'namespace':'AspisR1ScheduleEnclosingCandidate','helper_reference_map':mapping,'generator_sha256':sha(Path(__file__).read_bytes())},indent=2)+'\n');print(sha(q.read_bytes()))
