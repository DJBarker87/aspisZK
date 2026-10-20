fn pair(&self,alpha:&[E],f:&[u8],kappa:E)->Result<E,Error> {
        let n=f.len()/32; let folds=alpha.len();
        if n!=1024>>(2*folds) {return Err(Error::Parse);}
        let ap0=powers::<4>(alpha[0]);
        let ap1=if folds==2 {powers::<4>(alpha[1])}else{[E::ONE;4]};
        let mut scratch=aspis_core::r0::heap::filled(n,K::ZERO).map_err(|_|Error::Allocation)?;
        let mut parts=[E::ZERO;7];
        // On S2's two-fold path the high tensor factors for point rows 0 and
        // 2 are identical. Keep the equality guard so arbitrary constructed
        // `Weights` values retain the original per-row fallback.
        let shared_two_point = self.variant==Variant::S2 && folds==2
            && self.factors[0][2]==self.factors[2][2]
            && self.factors[0][3]==self.factors[2][3];
        for kind in [1usize,2,3,5,6] {
            if shared_two_point && (kind==1 || kind==3) { continue; }
            if self.variant==Variant::D && kind<4 {
                parts[kind]=self.dense_point_pair(kind,alpha,f)?;
            } else {
                let k=if kind<4 {kind-1}else{kind-2};
                self.tensor(k,folds,&mut scratch);
                let mut scale=Self::scalar_factor(&self.factors[k][0],&ap0);
                if folds==2 {scale=scale.mul(Self::scalar_factor(&self.factors[k][1],&ap1));}
                let mut pair=crate::fast_pairing::EbyKDot::new();
                for j in 0..n {pair.push(field(f,j),scratch[j]).map_err(|_|Error::Parse)?;}
                parts[kind]=scale.mul(pair.finish());
            }
        }
        if shared_two_point {
            // The two point rows share the d2/d3 coefficients. Preserve the
            // tensor's least-significant-first order: d2 is j mod 4 and d3
            // is j / 4. Each d4 slice then contracts one 16-term EbyKDot.
            let common:[K;16]=core::array::from_fn(|j|
                self.factors[0][2][j&3].mul(self.factors[0][3][j>>2]));
            let mut partials=[E::ZERO;4];
            for s in 0..4 {
                let mut dot=crate::fast_pairing::EbyKDot::new();
                for j in 0..16 {
                    dot.push(field(f,16*s+j),common[j]).map_err(|_|Error::Parse)?;
                }
                partials[s]=dot.finish();
            }
            for (kind,k) in [(1usize,0usize),(3usize,2usize)] {
                let mut high=crate::fast_pairing::EbyKDot::new();
                for s in 0..4 {
                    high.push(partials[s],self.factors[k][4][s]).map_err(|_|Error::Parse)?;
                }
                let scale=Self::scalar_factor(&self.factors[k][0],&ap0)
                    .mul(Self::scalar_factor(&self.factors[k][1],&ap1));
                parts[kind]=scale.mul(high.finish());
            }
        }
        if folds==1 {
            let dual:[E;16]=core::array::from_fn(|mask|(0..4).filter(|&s|mask&(1<<s)!=0).fold(E::ZERO,|v,s|v.add(ap0[PERM[s]])).mul_m31(QUARTER));
            let mut groups=[E::ZERO;16];
            for j in 0..n {
                let mut mask=0;
                for s in 0..4 {if self.raw(0,4*j+s)==K::ONE {mask|=1<<s;}}
                groups[mask]=groups[mask].add(field(f,j));
            }
            for m in 1..16 {parts[0]=parts[0].add(groups[m].mul(dual[m]));}
            for side in 0..2 {
                let p=kpowers::<5>(self.extra[side]);
                let scale=Self::scalar_factor(&[p[0],p[1],p[2],p[3]],&ap0);
                let mut power=K::ONE; let mut pair=E::ZERO;
                for j in 0..7 {pair=pair.add(field(f,j+7*side).mul_qm31(power));power=power.mul(p[4]);}
                parts[4]=parts[4].add(pair.mul(scale));
            }
        } else {
            // Two-fold 0/1 row: compute the sixteen challenge products once.
            // Coefficients with the same inactive mask share one subset sum.
            let low:[E;16]=core::array::from_fn(|s|ap0[PERM[s%4]].mul(ap1[PERM[s/4]]).mul_m31(QUARTER.mul(QUARTER)));
            parts[0]=grouped_inactive_pair(self,f,&low);
            let libra=if self.variant==Variant::S2 {factored_s2_libra_weights(&ap0,&ap1,self.extra)}else{twofold_libra_weights(&low,self.extra)};
            for j in 0..4 {parts[4]=parts[4].add(field(f,j).mul(libra[j]));}
        }
        #[cfg(feature="prover")]
        for kind in 0..7 {
            for j in 0..1024 {crate::trace::value(6,kind*1024+j,E::from_qm31(self.raw(kind,j)));}
            for j in 0..n {crate::trace::value(7,kind*n+j,self.dual_raw(kind,j,alpha));}
        }
        let k=powers::<7>(kappa);let mut sum=E::ZERO;
        for kind in 0..7 {crate::trace::value(8,kind,parts[kind]);sum=sum.add(k[kind].mul(parts[kind]));}
        Ok(sum)
    }