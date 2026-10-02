## run_r117_full.py — SHA256 753728d342264557d7690d83bd582e3ff662bcff0823eafa7a00d0dfd8491e96 (429 bytes)
```text
1: #!/usr/bin/env python3
2: """Focused private final-vector fold and complete verifier gates."""
3: from pathlib import Path
4: source=Path(__file__).with_name('run_r107_full.py').read_text()
5: source=source.replace("'r107_native'","'r117_native'")
6: source=source.replace('r107-semantic-check','r117-primal-check').replace('semantic-check.log','primal-check.log')
7: exec(compile(source,str(Path(__file__).with_name('run_r107_full.py')),'exec'))
```
## run_r107_full.py — SHA256 cc78a76cf99274e48e3c9447eb725e54a3582e370558e852fa40d959805ba57c (637 bytes)
```text
1: #!/usr/bin/env python3
2: """Focused changed semantic region, same fixture/full-execution gates."""
3: from pathlib import Path
4: source=Path(__file__).with_name('run_r106_full.py').read_text()
5: source=source.replace("'r106_native'","'r107_native'")
6: source=source.replace("    compile('r106-terminal-check');run('compact-check.log',[str(cache/'release/r106-terminal-check')])", "    shutil.copy2(control/'r24-host-a/compact-check.log',out/'compact-check.log')\n    compile('r107-semantic-check');run('semantic-check.log',[str(cache/'release/r107-semantic-check')])")
7: exec(compile(source,str(Path(__file__).with_name('run_r106_full.py')),'exec'))
```
## run_r106_full.py — SHA256 f21035a12aa82a51bfae3d7d662ddfd42bf67db4e7c6bf6c01adffbb5db63817 (1570 bytes)
```text
1: #!/usr/bin/env python3
2: """Same-proof terminal candidate, focused host then complete SBF/LiteSVM."""
3: from pathlib import Path
4: source=Path(__file__).with_name('run_r84_full.py').read_text()
5: source=source.replace("assert 'r84_compact' in m","assert 'r84_compact' in m and 'r106_native' in m")
6: source=source.replace("fixtures=[s/'r24-host-a'/f'fixture-world{w}'for w in range(2)]","fixtures=[Path(f['path'])for f in m['r106_native']['fixtures']]\nfor f,record in zip(fixtures,m['r106_native']['fixtures']):assert sha(f/'proof-1.bin')==record['sha256']")
7: old="    compile('r84-bitperm-check');run('compact-check.log',[str(cache/'release/r84-bitperm-check')])\n    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])"
8: new="""    control=Path(m['r106_native']['control']);cm=json.loads((control/'r18-stage.json').read_text())
9:     changed=[n for n,h in m['files'].items()if cm['files'].get(n)!=h]
10:     assert len(changed)==m['r106_native']['changed']
11:     shutil.copy2(control/'r24-host-a/opening-check.log',out/'opening-check.log')
12:     compile('r106-terminal-check');run('compact-check.log',[str(cache/'release/r106-terminal-check')])"""
```
## run_r84_full.py — SHA256 746a9e8b4acdae77308f17752278b718f37595b21bea7d27d55c342d631cb421 (5269 bytes)
```text
1: #!/usr/bin/env python3
2: """Full compact candidate experiment; NEW proofs/profile, never security promotion."""
3: import argparse,hashlib,json,os,shutil,subprocess,time
4: from pathlib import Path
5: p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--mode',choices=['host','sbf','svm'],required=True);a=p.parse_args()
6: s=a.stage.resolve();here=Path(__file__).parent
7: def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
8: m=json.loads((s/'r18-stage.json').read_text());assert 'r84_compact' in m
9: for n,h in m['files'].items():assert sha(s/n)==h,n
10: cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
11: caps={n:(cg/n).read_text().strip()for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
12: hi,ma={'host':(5,7),'sbf':(12,16),'svm':(2,3)}[a.mode]
13: assert caps=={'memory.high':str(hi*2**30),'memory.max':str(ma*2**30),'memory.swap.max':'0','pids.max':'128'}
14: out=s/f'r24-{a.mode}-a';assert not out.exists();out.mkdir();(out/'resources.json').write_text(json.dumps(caps,indent=2)+'\n')
15: env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
16: for n in list(env):
17:     if n.startswith('ASPIS_'):env.pop(n)
18: ex=s/'docs/research/v8-no-work-100-20260907/experiments'
19: cache=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
20: meta=json.loads((s/'r17-stage.json').read_text());records=[]
21: def run(name,cmd):
22:     print(json.dumps({'phase':name,'command':cmd}),flush=True);start=time.monotonic()
23:     with (out/name).open('w')as f:r=subprocess.run(['/usr/bin/time','-v']+cmd,env=env,cwd=s,stdout=f,stderr=subprocess.STDOUT)
24:     records.append({'name':name,'exit':r.returncode,'wall_s':time.monotonic()-start})
25:     (out/'commands.json').write_text(json.dumps(records,indent=2)+'\n');assert r.returncode==0,(name,r.returncode)
26: def compile(binary):
27:     run(binary+'-compile.log',['/home/dombarker/.cargo/bin/cargo','build','--offline','--locked','--release','--jobs','2','--features',meta['features'],'--manifest-path',str(ex/'performance-host/Cargo.toml'),'--bin',binary])
28: fixtures=[s/'r24-host-a'/f'fixture-world{w}'for w in range(2)]
29: if a.mode=='host':
30:     env.update(RUSTFLAGS=meta['rustflags'],CARGO_TARGET_DIR=str(cache))
31:     compile('r84-bitperm-check');run('compact-check.log',[str(cache/'release/r84-bitperm-check')])
32:     compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])
33:     compile('aspis-v8-performance-host');binary=out/'r84-host';shutil.copy2(cache/'release/aspis-v8-performance-host',binary)
34:     for w,f in enumerate(fixtures):
35:         env.update(ASPIS_R16_SELECTED_SECOND=str(w),ASPIS_V8_POSITIVE_CASE='honest')
36:         run(f'generate-world{w}.log',[str(binary),str(f)])
37:         run(f'world{w}.log',[str(binary),'--audit-existing',str(f)])
38:     run('wire-controls.log',['python3',str(here/'check_r19_wire_controls.py'),'--binary',str(binary),'--fixture',str(fixtures[0]),
39:         '--old-fixture','/home/dombarker/project-offloads/aspis-r19-channel-20260921-c/host-c/fixture-world0','--output',str(out/'wire-controls')])
40: elif a.mode=='sbf':
41:     assert 'compact_source_implemented=true' in (s/'r24-host-a/compact-check.log').read_text()
42:     for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED' in (s/f'r24-host-a/world{w}.log').read_text()
43:     run('compile.log',['python3',str(here/'build_r84_sbf.py'),'--stage',str(s),'--mode','primary'])
44:     unstripped=cache.parent.parent/'performance-sbf/target/sbpf-solana-solana/release/aspis_v8_performance_sbf.so'
45:     shutil.copy2(unstripped,s/'aspis-unstripped.so')
46: else:
47:     binary=Path('/home/dombarker/project-offloads/aspis-r20-svm-20260922-a/r20-svm-probe');elf=s/'sbf-primary/aspis_v8_performance_sbf.so'
48:     build=(s/'r24-sbf-a/compile.log').read_text();assert 'overflows the maximum allowed frame' not in build and not('Stack offset' in build and 'exceeded' in build)
```
## run_r118_source.py — SHA256 24d1741c42669873e839310699ad3b16bedc6934ef269e87a86361ea2c602cec (4134 bytes)
```text
25: (ex/'r118_primal_source.rs').write_text(helper);changed.append(ex/'r118_primal_source.rs')
26: cargo=ex/'performance-host/Cargo.toml';cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r118-source-boundary"\npath="../r118_source_boundary.rs"\n');changed.append(cargo)
27: for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
28: m['r118_boundary']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
29:  'changed':3,'verifier_changed':False,'profile_changed':False,'accepted_prefix':False,'universal_coverage':False,
30:  'full_security':False,'primal_helper_source_sha256':sha(ex/'r17_coupled_audit.rs'),
31:  'primal_helper_exact_prefix':True,'expected_heavy_step':'cached release compilation; only three 13-by-28 eliminations'}
32: (dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
33: out=dst/'check-a';out.mkdir();(out/'resources.json').write_text(json.dumps(caps,indent=2)+'\n')
34: meta=json.loads((src/'r17-stage.json').read_text());cache=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
35: env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTFLAGS=meta['rustflags'],CARGO_TARGET_DIR=str(cache),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
36: records=[]
37: def run(name,cmd):
38:     print(json.dumps({'phase':name,'command':cmd}),flush=True);start=time.monotonic()
39:     with(out/name).open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],env=env,cwd=dst,stdout=f,stderr=subprocess.STDOUT)
40:     records.append({'name':name,'command':cmd,'exit':r.returncode,'wall_s':time.monotonic()-start})
41:     (out/'commands.json').write_text(json.dumps(records,indent=2)+'\n');assert r.returncode==0,(name,r.returncode)
42: run('compile.log',['/home/dombarker/.cargo/bin/cargo','build','--offline','--locked','--release','--jobs','2','--features',meta['features'],'--manifest-path',str(cargo),'--bin','r118-source-boundary'])
43: binary=out/'r118-source-boundary';shutil.copy2(cache/'release/r118-source-boundary',binary)
44: run('check.log',[str(binary),str(out/'results')])
45: (out/'metadata.json').write_text(json.dumps({'source_manifest_sha256':sha(dst/'r18-stage.json'),'binary_sha256':sha(binary),'base_revision':'3a4a95e8a5f6d5ee1369c37ae6485ea2b32bf757','overflow_checks':True,'full_security':False},indent=2)+'\n')
```
## r18-stage.json — SHA256 26755a4250ec6075005e840565040414b694deb97fb1830fc95aff2692d34fb6 (70852 bytes)
## r17-stage.json — SHA256 5efe649ea258413090ba648313984b20312b4dafe4723984293ef36cb241077e (8777 bytes)
## host-metadata.json — SHA256 9104fbc77d1f9e168b8c23dbada8474c264dda7ce733c02a4d2f172a7be83eba (1207 bytes)
## BetaUniformCorrection.lean — SHA256 7af7a0aa8360d7938a6d20ebf1c0f275ddbbe389f1f4c9da1e96d103b476a6d0 (3756 bytes)
```text
42: /- For the source, I and J are (chunk, slot). A coefficient kernel is zero
43:    between chunks and outside the convolution diagonal. Reversed weight
44:    slots and the quarter factor belong to C, not to a new assumption. -/
45: def coefficient (C : I → J → F) (q : I → F) (w : J → F) : F :=
46:   ∑ i, ∑ j, C i j * q i * w j
47: 
48: theorem coefficient_left (C : I → J → F) (q r : I → F) (w : J → F)
49:     (a b : F) : coefficient C (fun i => a*q i+b*r i) w =
50:     a*coefficient C q w+b*coefficient C r w := by
51:   have term : ∀ i j, C i j*(a*q i+b*r i)*w j =
52:       a*(C i j*q i*w j)+b*(C i j*r i*w j) := by intros; ring
53:   simp only [coefficient, term, Finset.sum_add_distrib, Finset.mul_sum]
54: 
55: theorem coefficient_right (C : I → J → F) (q : I → F) (w v : J → F)
56:     (a b : F) : coefficient C q (fun j => a*w j+b*v j) =
57:     a*coefficient C q w+b*coefficient C q v := by
58:   have term : ∀ i j, C i j*q i*(a*w j+b*v j) =
59:       a*(C i j*q i*w j)+b*(C i j*q i*v j) := by intros; ring
60:   simp only [coefficient, term, Finset.sum_add_distrib, Finset.mul_sum]
61: 
62: theorem folded_coefficient_zero (C : I → J → F) (r g : I → F)
63:     (wr wg : J → F) (s beta : F)
64:     (hr : coefficient C r wr=0)
65:     (hc : coefficient C r wg+s*coefficient C g wr=0)
66:     (hg : coefficient C g wg=0) :
67:     coefficient C (fun i => (1-beta)*r i+s*beta*g i)
68:       (fun j => (1-beta)*wr j+beta*wg j)=0 := by
69:   rw [coefficient_left, coefficient_right, coefficient_right]
70:   have h := coefficient_zero (coefficient C r wr) (coefficient C r wg)
71:     (coefficient C g wr) (coefficient C g wg) s beta hr hc hg
72:   simpa only [mul_assoc] using h
73: end CoefficientModel
74: 
75: /- q_i is paired with w_(4-j)%4 by the retained reversed dual convention.
76:    Fin 4 ensures this is [0,3,2,1]. This model still needs a Rust semantics
77:    correspondence; no extraction of the loop or field code is claimed. -/
78: def sourceKernel (n k : Nat) (quarter : F)
79:     (i j : Fin n × Fin 4) : F :=
80:   if i.1=j.1 ∧ i.2.val+(4-j.2.val)%4=k then quarter else 0
81: 
82: #print axioms expansion
83: #print axioms coefficient_zero
84: #print axioms all_seven
85: #print axioms p2_retained
86: #print axioms coefficient_left
87: #print axioms coefficient_right
88: #print axioms folded_coefficient_zero
```
## FullCoefficientBoundary.lean — SHA256 66a7897879924c0f4dc99692e84cc9812104009a95e68e6c6908ef78fc7b136d (2753 bytes)
```text
1: import AspisV8R19.FullQuotientWeights
2: 
3: /-! Exact finite-field block-kernel restriction for all seven relation
4: coefficients. This is not a Rust word-semantics extraction. -/
5: namespace AspisR19.FullCoefficientBoundary
6: open AspisV8R16 AspisV8R17 BetaUniformCorrection FullQuotientWeights
7: open T163SourceTable NormalizedGCore HighRepairInvariant
8: noncomputable section
9: variable {F : Type*} [CommRing F]
10: 
11: theorem coefficient_blocks (n k : Nat) (quarter : F)
12:     (q w : Fin n × Fin 4 → F) :
13:     coefficient (sourceKernel n k quarter) q w =
14:       ∑ d : Fin n, ∑ s : Fin 4, ∑ t : Fin 4,
15:         (if s.val+(4-t.val)%4=k then quarter else 0)*q (d,s)*w (d,t) := by
16:   unfold coefficient
17:   rw [Fintype.sum_prod_type]
18:   apply Finset.sum_congr rfl
19:   intro d _
20:   apply Finset.sum_congr rfl
21:   intro s _
22:   rw [Fintype.sum_prod_type,Finset.sum_comm]
23:   apply Finset.sum_congr rfl
24:   intro t _
25:   simp [sourceKernel,ite_and,ite_mul]
26: 
27: def blockWeight (half a b c : F) (w : Fin 1024 → F) (i : Index 32) : F :=
28:   pointWeight half a b c w ⟨4*i.1.val+i.2.val,by omega⟩
29: 
30: theorem low_slot (q : Index 32 → F) (d : Fin 32) (s : Fin 4) :
31:     flatten q (4*d.val+s.val)=q (d,s) := by
32:   rw [flatten,dif_pos (show 4*d.val+s.val<128 by omega)]
33:   congr 1
34:   apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
35: 
36: theorem source_coefficient (half a b c tau quarter : F) (structured : Bool)
37:     (w : Fin 1024 → F) (q : Index 32 → F) (k : Nat) :
38:     coefficient (sourceKernel 256 k quarter)
39:       (fun i => flatten q (4*i.1.val+i.2.val))
40:       (fun i => sourceQuotientWeights half
41:         (extendFin1024 (transportDual inactive 1023 order w))
42:         a b c tau structured (4*i.1.val+i.2.val)) =
43:     coefficient (sourceKernel 32 k quarter) q (blockWeight half a b c w) := by
44:   rw [coefficient_blocks,coefficient_blocks,Fin.sum_univ_add (a:=32) (b:=224)]
45:   have hz : (∑ d : Fin 224, ∑ s : Fin 4, ∑ t : Fin 4,
46:       (if s.val+(4-t.val)%4=k then quarter else 0)*
47:         flatten q (4*(Fin.natAdd 32 d).val+s.val)*
48:         sourceQuotientWeights half (extendFin1024 (transportDual inactive 1023 order w))
49:           a b c tau structured (4*(Fin.natAdd 32 d).val+t.val))=0 := by
50:     apply Finset.sum_eq_zero
51:     intro d _
52:     apply Finset.sum_eq_zero
53:     intro s _
54:     apply Finset.sum_eq_zero
55:     intro t _
56:     simp [flatten,Fin.natAdd,show ¬4*(32+d.val)+s.val<128 by omega]
57:   rw [hz,add_zero]
58:   apply Finset.sum_congr rfl
59:   intro d _
60:   apply Finset.sum_congr rfl
61:   intro s _
62:   apply Finset.sum_congr rfl
63:   intro t _
64:   simp only [Fin.val_castAdd,low_slot]
65:   rw [quotient_entry half a b c tau structured w ⟨4*d.val+t.val,by omega⟩]
66:   rfl
67: 
68: #print axioms coefficient_blocks
69: #print axioms low_slot
70: #print axioms source_coefficient
71: end
72: end AspisR19.FullCoefficientBoundary
```
## AugmentedQuotient.lean — SHA256 5a844eea49a2b2c7d4189654862438cb823bdc878f2600d6b85ccc96113206b9 (5138 bytes)
```text
1: import AspisV8R19.AugmentedQuerySection
2: import AspisV8R19.NormalizedQuotient
3: import AspisV8R19.FullCoefficientBoundary
4: 
5: /-! The augmented section retains both complete seven-coefficient channel
6: maps, not just a post-beta mixture. Constant-low premises are explicit;
7: their two-swap source specialization is a separate certificate. -/
8: set_option autoImplicit false
9: namespace AspisR19.AugmentedQuotient
10: open HighRepairInvariant BetaUniformCorrection NormalizedQuotient
11: noncomputable section
12: variable {F : Type*} [Field F] [NeZero (2 : F)]
13: 
14: def lift (alpha : F) (s : Fin 4) (v : Fin 32 → F) (i : Index 32) : F :=
15:   v i.1 * slotFactor alpha s i.2
16: 
17: theorem lift_sum (alpha : F) (s : Fin 4) (v : Fin 32 → F) (i : Index 32) :
18:     lift alpha s v i = ∑ d, v d * column alpha d s i := by
19:   simp [lift,column,unit,slotFactor,Prod.ext_iff,ite_and,mul_sub,
20:     Finset.sum_sub_distrib,mul_ite]
21: 
22: theorem lift_point (alpha : F) (s : Fin 4) (v : Fin 32 → F) (w : Index 32 → F) :
23:     (∑ i, lift alpha s v i * w i) =
24:       ∑ d, v d * (w (d,s)-alpha^s.val*w (d,0)) := by
25:   simp only [lift_sum,Finset.sum_mul]
26:   rw [Finset.sum_comm]
27:   apply Finset.sum_congr rfl
28:   intro d _
29:   simp only [mul_assoc]
30:   rw [← Finset.mul_sum,column_point]
31: 
32: theorem lift_coefficient (quarter alpha : F) (s : Fin 4) (v : Fin 32 → F)
33:     (w : Index 32 → F) (k : Nat) :
34:     coefficient (sourceKernel 32 k quarter) (lift alpha s v) w =
35:       ∑ d, v d * localCoeff quarter alpha d s w k := by
36:   simp only [coefficient,lift_sum,Finset.mul_sum,Finset.sum_mul]
37:   calc
38:     _ = ∑ i, ∑ d, ∑ j, sourceKernel 32 k quarter i j * (v d * column alpha d s i) * w j := by
39:       apply Finset.sum_congr rfl
40:       intro i _
41:       rw [Finset.sum_comm]
42:     _ = ∑ d, ∑ i, ∑ j, sourceKernel 32 k quarter i j * (v d * column alpha d s i) * w j := by
43:       rw [Finset.sum_comm]
44:     _ = ∑ d, v d * coefficient (sourceKernel 32 k quarter) (column alpha d s) w := by
45:       apply Finset.sum_congr rfl
46:       intro d _
47:       simp only [coefficient,Finset.mul_sum]
48:       apply Finset.sum_congr rfl
49:       intro i _
50:       apply Finset.sum_congr rfl
51:       intro j _
52:       ring
53:     _ = _ := by simp only [column_coefficient]
54: 
55: def quotient (t : Fin 22 → F) (ht : Function.Injective t)
56:     (noneOne : ∀ i, t i ≠ 1) (alpha : F) (d : Fin 32) (s : Fin 4) : Index 32 → F :=
57:   lift alpha s (AugmentedQuerySection.normalized t ht noneOne d)
58: 
```
## SourceCircleBoundary.lean — SHA256 d0cf5ee7129708bd910a32a2e2a428a33f1aca12aca60b23c9da9e6569cbf091 (3781 bytes)
```text
1: import AspisV8R19.PreparedCircleFold
2: import AspisV8R19.SourceNormalizationBoundary
3: 
4: /-! The exact-field source normalization, evaluator, transport and prepared
5: fold now share one observation boundary. Source sampler and word refinement
6: are not smuggled in as assumptions about independent challenges. -/
7: namespace AspisR19.SourceCircleBoundary
8: open AspisV8R16 AspisCircleTensorBinding NormalizationLoopBridge
9: open SourceMaskTransport SourceEncodedOpening CircleObservationBridge PreparedCircleFold
10: noncomputable section
11: variable {F : Type*} [Field F] [NeZero (2 : F)]
12: 
13: def column (t : Fin 22 → F) (alpha : F) (j : Fin 13) :=
14:   sourceQuotient t alpha (SparseHighWitness.degree j) (SparseHighWitness.slot j)
15: 
16: theorem coefficient_fold_zero (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F) (j : Fin 13) :
17:     ∀ i, ∑ k : Fin 4, alpha^k.val*column t alpha j (i,k)=0 := by
18:   rw [column,selected_sourceQuotient_eq t ht alpha j]
19:   exact NormalizedQuotient.quotient_fold t ht alpha _ _
20: 
21: theorem raw_point_zero (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
22:     (j : Fin 13) (rootIndex : Fin 22) (a b c x y : F)
23:     (circle : x^2+y^2=1) (root : doubledFactor x 1=t rootIndex) :
24:     sourceMaskEvaluate (mask (2:F)⁻¹ a b c (column t alpha j)) x y=0 := by
25:   rw [column,selected_sourceQuotient_eq t ht alpha j]
26:   exact mask_root_zero t ht alpha _ _ rootIndex a b c x y circle root
27: 
```
## R241CoeffExecution.lean — SHA256 6df2ae8b3a73cde7f0973451a54e8b6b093ab54f61a98d6193da62a8f6ade73f (2944 bytes)
```text
1: import AspisR239CoeffExecutionRaw
2: import AspisV8R19.R222NormLeafExecution
3: import AspisV8R19.R240HalfExecution
4: 
5: /-! Exact execution of the selected coefficient constructor and four-value
6: coefficient evaluator.  These theorems describe only the raw leaves. -/
7: set_option autoImplicit false
8: namespace AspisV8R19.R241CoeffExecution
9: open Aeneas Aeneas.Std Result
10: open AspisV8R15.ExactTowerBase
11: open AspisR239CoeffExecutionRaw
12: open AspisV8R19.R240HalfExecution (mapBase)
13: noncomputable section
14: 
15: theorem coeff_new_exact (a b c : QM31Exact) :
16:     circle_norm.Coeff.new
17:       (Array.make 3#usize [R164ProductExecution.encode a,
18:         R164ProductExecution.encode b, R164ProductExecution.encode c]) =
19:     .ok (Array.make 5#usize [
20:       R163ComplexExecution.encode (NormInverse.quarticNorm a + NormInverse.quarticNorm c),
21:       R163ComplexExecution.encode (NormInverse.quarticNorm b - NormInverse.quarticNorm c),
22:       R163ComplexExecution.encode (R218CircleNormAlgebra.polar a b),
23:       R163ComplexExecution.encode (R218CircleNormAlgebra.polar a c),
24:       R163ComplexExecution.encode (R218CircleNormAlgebra.polar b c)]) := by
25:   simp [circle_norm.Coeff.new, Array.index_usize, Array.make,
26:     R222NormLeafExecution.norm_exact, R222NormLeafExecution.polar_exact,
27:     R163ComplexExecution.cm_add, R163ComplexExecution.cm_sub, bind_tc_ok]
28: 
29: theorem mapBase_mul (u v : M31Exact) :
30:     mapBase (u*v) = mapBase u * mapBase v := by
31:   apply QuadraticAlgebra.ext <;>
32:     simp [mapBase,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
33: 
34: theorem coeff_four_exact (a b c : QM31Exact) (x y : M31Exact) :
35:     circle_norm.Coeff.four
36:       (Array.make 5#usize [
37:         R163ComplexExecution.encode (NormInverse.quarticNorm a + NormInverse.quarticNorm c),
38:         R163ComplexExecution.encode (NormInverse.quarticNorm b - NormInverse.quarticNorm c),
39:         R163ComplexExecution.encode (R218CircleNormAlgebra.polar a b),
40:         R163ComplexExecution.encode (R218CircleNormAlgebra.polar a c),
41:         R163ComplexExecution.encode (R218CircleNormAlgebra.polar b c)])
42:       (ComplexBaseExecution.encodeBase x) (ComplexBaseExecution.encodeBase y) =
43:     .ok (Array.make 4#usize [
44:       R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).1),
45:       R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.1),
46:       R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.2.1),
47:       R163ComplexExecution.encode ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.2.2)]) := by
48:   simp [circle_norm.Coeff.four, Array.index_usize, Array.make,
49:     R161WrappedMulExecution.mul_encode, R240HalfExecution.cm_mul_m31_exact,
50:     R163ComplexExecution.cm_add, R163ComplexExecution.cm_sub, bind_tc_ok,
51:     R218CircleNormAlgebra.four,mapBase_mul,pow_two]
52: 
53: #print axioms coeff_new_exact
54: #print axioms mapBase_mul
55: #print axioms coeff_four_exact
56: end
57: end AspisV8R19.R241CoeffExecution
```
## R270PrivateCoefficientExecution.lean — SHA256 2c8cf97328300c8d9e71dc4427d1512baec70f1b4d1b202400780eaaf2c0c55d (2873 bytes)
```text
1: import AspisV8R19.R265PrivateNormClosures
2: import AspisV8R19.R260PrivateInputExecution
3: import AspisV8R19.R242LineCoeffExecution
4: 
5: /-! Actual private coefficient constructor/evaluator on canonical encodings.
6: The constructor's Option input calls and exact two closure executions remain
7: in the raw definition. This does not prove its vector consumers or inversion. -/
8: set_option autoImplicit false
9: namespace AspisV8R19.R270PrivateCoefficientExecution
10: open Aeneas Aeneas.Std Result
11: open AspisV8R15.ExactTowerBase
12: open AspisR264PrivateCoefficientRaw.circle_norm.joined_inverse.line_norm.r110_norm (Coeff110)
13: open R250PrivateBaseExecution (encodeC)
14: open R240HalfExecution (mapBase)
15: noncomputable section
16: 
17: def coefficients (a b c : QM31Exact) : Coeff110 :=
18:   Array.make 5#usize [
19:     encodeC (NormInverse.quarticNorm a+NormInverse.quarticNorm c+
20:       (NormInverse.quarticNorm b-NormInverse.quarticNorm c)/2),
21:     encodeC ((NormInverse.quarticNorm b-NormInverse.quarticNorm c)/2),
22:     encodeC (R218CircleNormAlgebra.polar a b),
23:     encodeC (R218CircleNormAlgebra.polar a c),
24:     encodeC (R218CircleNormAlgebra.polar b c)]
25: 
26: theorem coeff_new_exact (a b c : QM31Exact) :
27:     Coeff110.new (Array.make 3#usize [R164ProductExecution.encode a,
28:       R164ProductExecution.encode b,R164ProductExecution.encode c]) =
29:         .ok (some (coefficients a b c)) := by
30:   have hn := R265PrivateNormClosures.norm_exact
31:   have hp := R265PrivateNormClosures.polar_exact
32:   simp only [R265PrivateNormClosures.privateParts,Array.make] at hn hp
33:   simp [Coeff110.new,Array.index_usize,Array.make,R164ProductExecution.encode,
34:     R260PrivateInputExecution.input_encoded,R260PrivateInputExecution.branch_some,
35:     hn,hp,
36:     R252PrivateComplexLinear.c_sub,R252PrivateComplexLinear.c_add,
37:     R252PrivateComplexLinear.c_half,coefficients,bind_tc_ok]
38: 
39: theorem coeff_four_exact (a b c : QM31Exact) (x y t : M31Exact) :
40:     Coeff110.four (coefficients a b c)
41:       (ComplexBaseExecution.encodeBase x) (ComplexBaseExecution.encodeBase y)
42:       (ComplexBaseExecution.encodeBase t) =
43:         .ok (Array.make 4#usize [
44:           encodeC ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).1),
45:           encodeC ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).2.1),
46:           encodeC ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).2.2.1),
47:           encodeC ((R225LineNormAlgebra.lineFour a b c (mapBase x) (mapBase y) (mapBase t)).2.2.2)]) := by
48:   simp [Coeff110.four,coefficients,Array.index_usize,Array.make,
49:     R250PrivateBaseExecution.mul_encoded,R252PrivateComplexLinear.c_mul_m,
50:     R252PrivateComplexLinear.c_add,R252PrivateComplexLinear.c_sub,
51:     R225LineNormAlgebra.lineFour,R241CoeffExecution.mapBase_mul,bind_tc_ok]
52: 
53: #print axioms coeff_new_exact
54: #print axioms coeff_four_exact
55: end
```
## R271PrivateLineNormBridge.lean — SHA256 250ceecef34da45446e0982a72c1a5d3e74c2955e6a650620109b45f6e3050b3 (2668 bytes)
```text
1: import AspisV8R19.R270PrivateCoefficientExecution
2: import AspisV8R19.R243LineNormBridge
3: 
4: /-! The private coefficient evaluator at the already-proved source line
5: coordinate. Explicit unit-circle premise; no selected pointer/vector or
6: whole try_norm/callback correspondence is asserted. -/
7: set_option autoImplicit false
8: namespace AspisV8R19.R271PrivateLineNormBridge
9: open Aeneas Aeneas.Std Result
10: open AspisV8R15.ExactTowerBase
11: open AspisR264PrivateCoefficientRaw.circle_norm.joined_inverse.line_norm.r110_norm (Coeff110)
12: open R250PrivateBaseExecution (encodeC)
13: open ComplexBaseExecution (encodeBase)
14: open R240HalfExecution (mapBase)
15: noncomputable section
16: 
17: theorem private_line_four (a b c : QM31Exact) (x y : M31Exact) :
18:     Coeff110.four (R270PrivateCoefficientExecution.coefficients a b c)
19:       (encodeBase x) (encodeBase y) (encodeBase (2*x^2-1)) =
20:         .ok (Array.make 4#usize [
21:           encodeC ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).1),
22:           encodeC ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.1),
23:           encodeC ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.2.1),
24:           encodeC ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.2.2)]) := by
25:   rw [R270PrivateCoefficientExecution.coeff_four_exact,
26:     R243LineNormBridge.mapBase_line,R225LineNormAlgebra.lineFour_eq]
27: 
28: theorem mapped_circle (x y : M31Exact) (hcircle : x^2+y^2=1) :
29:     (mapBase x)^2+(mapBase y)^2=1 := by
30:   have hr1 : (1 : CM31Exact).re = (1 : M31Exact) := rfl
31:   have hi1 : (1 : CM31Exact).im = 0 := rfl
32:   apply QuadraticAlgebra.ext
33:   · simpa [mapBase,pow_two,QuadraticAlgebra.re_mul,hr1] using hcircle
34:   · simp [mapBase,pow_two,QuadraticAlgebra.im_mul,hi1]
35: 
36: theorem private_line_norms (a b c : QM31Exact) (x y : M31Exact)
37:     (hcircle : x^2+y^2=1) :
38:     Coeff110.four (R270PrivateCoefficientExecution.coefficients a b c)
39:       (encodeBase x) (encodeBase y) (encodeBase (2*x^2-1)) =
40:         .ok (Array.make 4#usize [
41:           encodeC (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (mapBase x) (mapBase y))),
42:           encodeC (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (mapBase x) (-mapBase y))),
43:           encodeC (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (-mapBase x) (-mapBase y))),
44:           encodeC (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (-mapBase x) (mapBase y)))]) := by
45:   rw [private_line_four,
46:     R218CircleNormAlgebra.four_exact a b c (mapBase x) (mapBase y) (mapped_circle x y hcircle)]
47: 
48: #print axioms private_line_four
49: #print axioms mapped_circle
50: #print axioms private_line_norms
51: end
52: end AspisV8R19.R271PrivateLineNormBridge
```
