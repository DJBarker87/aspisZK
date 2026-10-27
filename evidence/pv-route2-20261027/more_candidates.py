from pathlib import Path
import json,difflib
D=Path('evidence/pv-route2-20261027');rows=json.loads((D/'candidates.json').read_text());S=D/'source-inputs';S.mkdir(exist_ok=True)
def save(op,path,new,kind,chain):
 old=Path(path).read_text();(D/'patches'/f'{op}.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path)))
 q=S/str(op)/path;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(new)
 t=(D/'patches'/f'{op}.patch').read_text().splitlines(); rows.append(dict(op=op,kind=kind,callers=chain,added=sum(x.startswith('+') and not x.startswith('+++') for x in t),removed=sum(x.startswith('-') and not x.startswith('---') for x in t),measurement='isolated modified source dependency, not adoption'))
p='crates/aspis-core/src/r0/encoder.rs';s=Path(p).read_text();s=s.replace('    for (pair, n) in q.chunks_exact(2).zip(basis) {\n        p0 = p0.add(pair[0].mul(n));\n        p1 = p1.add(pair[1].mul(n));\n    }','    let mut i = 0usize;\n    while i < 512 {\n        let n = basis[i];\n        p0 = p0.add(q[2*i].mul(n));\n        p1 = p1.add(q[2*i+1].mul(n));\n        i += 1;\n    }');save(79,p,s,'prover-local',['prover::eval_message','host_semantic::build','sim::eval_message','copy eval_pair and basis::values'])
p='crates/aspis-core/src/state_only_sumcheck.rs';s=Path(p).read_text();a=s.index('    let block_value = |block: usize|');b=s.index('    let mut accumulator = block_value(6);',a);s=s[:a]+'''    fn block_value(polynomial: &StateOnlySumcheckPolynomial, powers: [QM31;3], block:usize)->QM31 {
        let start=4*block;
        polynomial[start].add(qm31_sum_products3(powers,[polynomial[start+1],polynomial[start+2],polynomial[start+3]]))
    }
'''+s[b:];s=s.replace('block_value(6)','block_value(polynomial,powers,6)').replace('block_value(block)','block_value(polynomial,powers,block)');save(121,p,s,'prover-local',['copy state-only sumcheck consumers from host prover','evaluate_state_only_polynomial::block_value','qm31_sum_products3 and PreparedQm31Multiplier'])
p='crates/aspis-core/src/state_only_hiding.rs';s=Path(p).read_text();s=s.replace('    for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {\n        coefficients','    let mut column=0usize;\n    while column < STATE_ONLY_HIDING_C1_COLUMNS {\n        coefficients',1).replace('mul_tower_basis(c1[column], column & 3);\n    }','mul_tower_basis(c1[column], column & 3);\n        column += 1;\n    }',1);s=s.replace('    for column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {\n        coefficients','    let mut column=0usize;\n    while column < STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {\n        coefficients',1).replace('mul_tower_basis(mask_only_c1[column], column & 3);\n    }','mul_tower_basis(mask_only_c1[column], column & 3);\n        column += 1;\n    }',1);s=s.replace('    for exponent in (0..STATE_ONLY_HIDING_FACTOR_DEGREE).rev() {\n        shared','    let mut exponent=STATE_ONLY_HIDING_FACTOR_DEGREE;\n    while exponent > 0 {\n        exponent -= 1;\n        shared',1);save(117,p,s,'prover-local',['host prover mask terminal consumers','selected_mask_linears','mul_tower_basis','mask_power_26','PreparedQm31Multiplier'])
p='crates/aspis-statement/src/constraints_v4.rs';s=Path(p).read_text();a=s.index('    let trailing_boolean = point');b=s.index('    let mut weights =',a);s=s[:a]+'''    let mut prefix_len=point.len();
    while prefix_len > 0 && (point[prefix_len-1] == QM31::ZERO || point[prefix_len-1] == QM31::ONE) {prefix_len-=1;}
    let trailing_boolean=point.len()-prefix_len;
    let mut suffix=0usize;
    let mut coordinate=prefix_len;
    while coordinate < point.len() {suffix=(suffix<<1)|usize::from(point[coordinate]==QM31::ONE);coordinate+=1;}
'''+s[b:];s=s.replace('        for (coordinate, value) in point[..prefix_len].iter().enumerate() {','        let mut coordinate=0usize;\n        while coordinate < prefix_len {\n            let value=point[coordinate];').replace('QM31::ONE.sub(*value)\n            } else {\n                *value','QM31::ONE.sub(value)\n            } else {\n                value').replace('        weights.push((row, weight));','        weights.push((row, weight));');s=s.replace('''                value
            });
        }
        weights.push''','''                value
            });
            coordinate+=1;
        }
        weights.push''');a=s.index('    Some(\n        sparse_eq_weights(point)');b=s.index('\n}\n',a);s=s[:a]+'''    let weights=sparse_eq_weights(point);
    let mut sum=QM31::ZERO;
    let mut i=0usize;
    while i < weights.len() { let (row,weight)=weights[i];sum=sum.add(weight.mul(column[row]));i+=1; }
    Some(sum)'''+s[b:];save(222,p,s,'prover-local',['host_semantic::multilinear_evaluate_qm31 consumers','sparse_eq_weights (Vec retained)'])
p='crates/aspis-r1-cost-probe/src/weights.rs';s=Path(p).read_text();s=s.replace('(0..10).fold(K::ONE,|v,b|v.mul(if r&(1<<b)==0 {K::ONE.sub(self.points[kind-1][9-b])}else{self.points[kind-1][9-b]}))','{let mut v=K::ONE;let mut b=0usize;while b<10 {v=v.mul(if r&(1<<b)==0 {K::ONE.sub(self.points[kind-1][9-b])}else{self.points[kind-1][9-b]});b+=1;}v}').replace('(0..5).fold(K::ONE,|v,d|v.mul(self.factors[k][d][(j>>(2*d))&3]))','{let mut v=K::ONE;let mut d=0usize;while d<5 {v=v.mul(self.factors[k][d][(j>>(2*d))&3]);d+=1;}v}');save(253,p,s,'in-place',['Weights::materialize','Weights::dual_raw','Weights::pair'])
s=s.replace('for (j,v) in w.iter_mut().enumerate() {for kind in 0..7 {*v=v.add(kp[kind].mul_qm31(self.raw(kind,j)));}}','let mut j=0usize;\n        while j<w.len() {let mut kind=0usize;while kind<7 {w[j]=w[j].add(kp[kind].mul_qm31(self.raw(kind,j)));kind+=1;}j+=1;}').replace('  if i==N { return out; }\n  p=p.mul(x);','  if i<N { p=p.mul(x); }');save(251,p,s,'in-place',['prover materialize consumers','Weights::raw','powers','heap::filled'])
# new is already index based; remove IntoIterator Range from its factor construction.
s=Path(p).read_text();a=s.index('        for k in 0..3 { for d in 0..5 {');b=s.index('        Ok(Self::box_from_parts',a);s=s[:a]+'''        let mut k=0usize;
        while k<3 {let mut d=0usize;while d<5 {
            let a=points[k][9-2*TAU[d]];let b=points[k][8-2*TAU[d]];
            factors[k][d]=[K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)];d+=1;
        }k+=1;}
        let mut k=0usize;
        while k<2 {
            factors[3+k][0]=[K::ONE,z[k].y,z[k].x,z[k].x.mul(z[k].y)];
            let mut x=double(z[k].x);let mut d=1usize;
            while d<5 {let y=double(x);factors[3+k][d]=[K::ONE,x,y,x.mul(y)];x=double(y);d+=1;}
            k+=1;
        }
'''+s[b:];save(252,p,s,'in-place',['prover Weights::new consumers','box_from_parts retains Box ownership','state_only_prefix::statement_points'])
(D/'candidates.json').write_text(json.dumps(rows,indent=2)+'\n')
