use super::*;
pub(super) fn dot(a: &[K], b: &[K]) -> K {
        assert_eq!(a.len(), b.len());
        a.iter().zip(b).fold(K::ZERO, |s, (&a, &b)| s.add(a.mul(b)))
    }
fn xt(v: &[K]) -> Vec<K> {
        let mut out = vec![K::ZERO; v.len() + 1];
        for (j, &value) in v.iter().enumerate() {
            let (mut row, mut bit, mut scale) = (j, 0, M31::ONE);
            while row & (1 << bit) != 0 {
                row ^= 1 << bit;
                scale = scale.mul(corelib::field::M31_HALF);
                out[row] = out[row].add(value.mul_m31(scale));
                bit += 1;
            }
            out[row | (1 << bit)] = out[row | (1 << bit)].add(value.mul_m31(scale));
        }
        out
    }
pub(super) fn chord(q: &[K], [a, b, c]: [K; 3]) -> Vec<K> {
        let e: Vec<_> = q.chunks_exact(2).map(|v| v[0]).collect();
        let o: Vec<_> = q.chunks_exact(2).map(|v| v[1]).collect();
        let xe = xt(&e);
        let xo = xt(&o);
        let xxo = xt(&xo);
        let get = |v: &[K], i| v.get(i).copied().unwrap_or(K::ZERO);
        let mut out = vec![K::ZERO; 1028];
        for i in 0..514 {
            out[2 * i] = a
                .mul(get(&e, i))
                .add(b.mul(get(&xe, i)))
                .add(c.mul(get(&o, i).sub(get(&xxo, i))));
            out[2 * i + 1] = c
                .mul(get(&e, i))
                .add(a.mul(get(&o, i)))
                .add(b.mul(get(&xo, i)));
        }
        assert!(out[1024..].iter().all(|&v| v == K::ZERO));
        out.truncate(1024);
        out
    }
pub(super) fn qvector(x: &[K], abc: [K; 3]) -> Vec<K> {
        let mut q = x[..1021].to_vec();
        q.extend([abc[1].mul(x[1021]), abc[2].mul(x[1021]), K::ZERO]);
        q
    }
pub(super) fn eval_weights(x: K, y: K) -> Vec<K> {
        let mut factors = [K::ZERO; 10];
        factors[0] = y;
        factors[1] = x;
        for i in 2..10 {
            factors[i] = factors[i - 1].square().mul_m31(M31(2)).sub(K::ONE);
        }
        (0..1024)
            .map(|j| {
                (0..10)
                    .filter(|&i| j & (1 << i) != 0)
                    .fold(K::ONE, |a, i| a.mul(factors[i]))
            })
            .collect()
    }
