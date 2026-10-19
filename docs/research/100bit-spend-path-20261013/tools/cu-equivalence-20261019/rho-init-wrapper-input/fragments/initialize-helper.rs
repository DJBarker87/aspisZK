fn initialize_weights(raw:&mut Vec<[u64;4]>,weights:&[K]) {
        for (out,w) in raw.iter_mut().zip(weights) {
            *out=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];
        }
}
