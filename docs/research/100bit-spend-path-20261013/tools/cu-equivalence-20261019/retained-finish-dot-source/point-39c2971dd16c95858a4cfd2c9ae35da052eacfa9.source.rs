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
