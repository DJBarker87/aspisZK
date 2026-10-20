//! Executable certificate, not a kernel certificate or an SBF execution proof.
//! Includes the frozen fast-domain and variant transport source without edits.
#[path = "../../../crates/aspis-r1-cost-probe/src/fast_domain.rs"]
mod fast_domain;
#[path = "../../../crates/aspis-r1-cost-probe/src/transport.rs"]
mod transport;

#[cfg(test)]
mod tests {
    use super::*;
    use aspis_core::{field::M31, r0::{domain, transport as d13}};
    const P: u64 = 2_147_483_647;
    type Point = (u64, u64);
    // Independent arithmetic: u128 products and Euclidean signed reduction,
    // rather than the shipped M31 reducer or CM31 multiplication.
    fn mul(a: Point, b: Point) -> Point {
        let x = (a.0 as i128 * b.0 as i128 - a.1 as i128 * b.1 as i128)
            .rem_euclid(P as i128) as u64;
        let y = ((a.0 as u128 * b.1 as u128 + a.1 as u128 * b.0 as u128)
            % P as u128) as u64;
        (x, y)
    }
    fn power(mut n: u64) -> Point {
        let mut a = (1, 0);
        let mut b = (2, 1_268_011_823);
        while n > 0 {
            if n % 2 == 1 { a = mul(a, b); }
            b = mul(b, b);
            n /= 2;
        }
        a
    }
    fn rev(mut n: usize, bits: usize) -> usize {
        let mut out = 0;
        for _ in 0..bits { out = out * 2 + n % 2; n /= 2; }
        out
    }
    fn double_x(x: u64) -> u64 { (2 * (x as u128 * x as u128 % P as u128) + P as u128 - 1) as u64 % P }
    fn bytes(p: Point) -> [u8; 8] {
        let mut out = [0; 8];
        out[..4].copy_from_slice(&(p.0 as u32).to_le_bytes());
        out[4..].copy_from_slice(&(p.1 as u32).to_le_bytes());
        out
    }
    fn literal_table(name: &str) -> Vec<Point> {
        let text = include_str!("../../../crates/aspis-r1-cost-probe/src/fast_domain.rs");
        let marker = format!("const {name}: [(u32, u32); 512] = [");
        let body = text.split_once(&marker).expect("exact table declaration").1
            .split_once("];" ).unwrap().0;
        let numbers: Vec<u64> = body.split(|c: char| !c.is_ascii_digit())
            .filter(|s| !s.is_empty()).map(|s| s.parse().unwrap()).collect();
        assert_eq!(numbers.len(), 1024);
        numbers.chunks_exact(2).map(|p| (p[0], p[1])).collect()
    }
    #[test]
    fn stored_tables_all_entries_from_closed_form() {
        for (name, offset, stride) in [("TABLE_A", 1024, 2097152), ("TABLE_B", 0, 4096)] {
            for (i, p) in literal_table(name).into_iter().enumerate() {
                assert!(p.0 < P && p.1 < P);
                assert_eq!(bytes(p), bytes(power(offset + stride * rev(i, 9) as u64)), "{name}[{i}]");
            }
            println!("PASS {name}: 512 entries / 4096 little-endian bytes, closed form");
        }
    }
    #[test]
    fn native_geometry_every_index() {
        for u in 0..262144 {
            let index = domain::FibreIndex::new(u).unwrap();
            let r = rev(u, 18);
            assert_eq!(domain::rev18(index), r);
            assert_eq!(r, 512 * rev(u % 512, 9) + rev(u / 512, 9));
            let expected = power(1024 + 4096 * r as u64);
            let native = fast_domain::fibre_point(index);
            assert_eq!(bytes((native.x.0 as u64, native.y.0 as u64)), bytes(expected));
            let core = domain::fibre_point::<M31>(index);
            assert_eq!(native, core);
            assert_eq!(fast_domain::line_node(index).0 as u64, double_x(expected.0));
            assert_eq!(fast_domain::line_node(index), domain::line_node::<M31>(index));
            for s in 0..4 {
                let slot = domain::SlotIndex::new(s).unwrap();
                let child = domain::child_index(index, slot);
                assert_eq!(child.get(), 4*u+s);
                assert_eq!(domain::parent_index(child), index);
                assert_eq!(domain::slot_index(child), slot);
                let natural = match s {0=>2*r, 1=>1048575-2*r, 2=>524288+2*r, _=>524287-2*r};
                assert_eq!(domain::natural_index(child), natural);
                let p = domain::stored_point::<M31>(child);
                assert_eq!(bytes((p.x.0 as u64,p.y.0 as u64)), bytes(power(1024*(2*natural+1) as u64)));
            }
        }
        // QueryGeometry's line x/y/z, all 65536 possible parents.
        for v in 0..65536 {
            let x = fast_domain::line_node(domain::FibreIndex::new(4*v).unwrap()).0 as u64;
            let y = fast_domain::line_node(domain::FibreIndex::new(4*v+3).unwrap()).0 as u64;
            let z = double_x(x);
            let r = rev(v,16) as u64;
            assert_eq!(x,power(2048+8192*r).0);
            assert_eq!(y,power(2048+8192*r+3*536870912).0);
            assert_eq!(z,power(4096+16384*r).0);
            assert!(x != 0 && y != 0 && z != 0);
            assert_eq!(double_x(z),power(8192+32768*r).0);
        }
        println!("PASS 262144 fibres, 1048576 stored slots, 65536 line parents; native functions against independent powers");
    }
    #[test]
    fn transport_tables_and_maps() {
        assert_eq!(transport::TAU, [3,4,2,0,1]);
        let pads: Vec<usize> = (0..89).map(|i| 16*(i/3)+13+i%3).collect();
        assert_eq!(d13::PAD_ROWS.map(usize::from).as_slice(),pads.as_slice());
        let mut order = pads.clone();
        order.extend((0..1023).filter(|r| !pads.contains(r)));
        order.push(1023);
        assert_eq!(order.len(),1024);
        let mut seen = [false;1024];
        for j in 0..1024 {
            assert_eq!(d13::COEFFICIENT_TO_ROW[j] as usize, order[j]);
            assert!(!seen[order[j]]); seen[order[j]]=true;
            assert_eq!(d13::ROW_TO_COEFFICIENT[order[j]] as usize,j);
            assert_eq!(transport::Variant::D.row(j),order[j]);
            let digits: Vec<_> = (0..5).map(|k| j/4usize.pow(k)%4).collect();
            let expected = 64*digits[0]+256*digits[1]+16*digits[2]+digits[3]+4*digits[4];
            for variant in [transport::Variant::S1,transport::Variant::S2] {
                assert_eq!(variant.row(j),expected);
                assert_eq!(variant.row(variant.row(j)),j);
            }
        }
        println!("PASS PAD_ROWS 89; D13 order/inverse 1024 each; TAU 5; S1/S2 row maps 1024 each");
    }
}
