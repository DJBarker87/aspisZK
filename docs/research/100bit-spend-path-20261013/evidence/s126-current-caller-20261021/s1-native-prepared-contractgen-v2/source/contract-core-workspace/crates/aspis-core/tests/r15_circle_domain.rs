//! Exhaustive concrete source-domain evidence, not an oracle/privacy theorem.
//! Independent u128 arithmetic checks the selected log-20 routine and tables.
use aspis_core::circle_fri::{
    selected_circle_fiber_points_shared, V6_CIRCLE_HIGH6_WINDOW, V6_CIRCLE_LOW6_WINDOW,
    V6_CIRCLE_MIDDLE6_WINDOW,
};

const P: u128 = 2_147_483_647;

fn checked_circle([x, y]: [u32; 2]) {
    assert!((x as u128) < P && (y as u128) < P);
    assert_eq!(((x as u128).pow(2) + (y as u128).pow(2)) % P, 1);
}

fn independent_add([x, y]: [u32; 2], [a, b]: [u32; 2]) -> [u32; 2] {
    let (x, y, a, b) = (x as u128, y as u128, a as u128, b as u128);
    [
        ((x * a + P * P - y * b) % P) as u32,
        ((x * b + y * a) % P) as u32,
    ]
}

#[test]
fn r15_all_log20_fibres_are_canonical_circle_points() {
    for table in [
        V6_CIRCLE_LOW6_WINDOW,
        V6_CIRCLE_MIDDLE6_WINDOW,
        V6_CIRCLE_HIGH6_WINDOW,
    ] {
        for point in table {
            checked_circle(point);
        }
    }
    let mut checked = 0;
    // Small reversed batches test caller order and avoid a large allocation.
    for start in (0u32..1 << 18).step_by(512) {
        let ids: Vec<_> = (start..start + 512).rev().collect();
        let actual = selected_circle_fiber_points_shared(20, &ids).unwrap();
        assert_eq!(actual.len(), ids.len());
        for (&id, point) in ids.iter().zip(actual) {
            let natural = id.reverse_bits() >> 14;
            let mut expected = V6_CIRCLE_LOW6_WINDOW[(natural & 63) as usize];
            let mid = ((natural >> 6) & 63) as usize;
            let high = (natural >> 12) as usize;
            if mid != 0 {
                expected = independent_add(expected, V6_CIRCLE_MIDDLE6_WINDOW[mid]);
            }
            if high != 0 {
                expected = independent_add(expected, V6_CIRCLE_HIGH6_WINDOW[high]);
            }
            assert_eq!([point.x.0, point.y.0], expected, "fibre {id}");
            checked_circle(expected);
            assert_ne!(expected[0], 0, "zero x at fibre {id}");
            assert_ne!(expected[1], 0, "zero y at fibre {id}");
            checked += 1;
        }
    }
    assert_eq!(checked, 262_144);
}
