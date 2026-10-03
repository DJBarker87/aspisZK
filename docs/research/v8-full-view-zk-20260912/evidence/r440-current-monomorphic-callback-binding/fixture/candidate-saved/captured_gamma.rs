#![allow(dead_code)]

fn invoke<F>(f: &mut F, acc: u32, value: &u32) -> u32
where
    F: FnMut(u32, &u32) -> u32,
{
    f(acc, value)
}

pub fn gamma_step(gamma: u32, acc: u32, value: &u32) -> (u32, u32) {
    let mut power = 1u32;
    let mut callback = |a: u32, v: &u32| {
        let weighted = power * *v;
        let result = a + weighted;
        power *= gamma;
        result
    };
    let result = invoke(&mut callback, acc, value);
    (result, power)
}
