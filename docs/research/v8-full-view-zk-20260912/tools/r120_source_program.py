"""Export the fixed new-profile boundary, without changing verifier source."""
from r119_source_program import build as previous

def build(s):
    s = previous(s).replace('r119_primal_source.rs', 'r120_primal_source.rs')
    # R119 retained an inherited, misleading JSON field name. The assertion
    # checks constancy, not zero: record the corrected schema without erasing
    # R119's original evidence.
    s = s.replace('\\"low_zero\\":{}', '\\"constant_low_map\\":{}')
    anchor = '        let channel_low=[&rw,&gw]'
    assert s.count(anchor) == 1
    s = s.replace(anchor, '''        let code_weights:Vec<Vec<u32>>=weights.iter().map(|w|map.dual(w)[..131].iter().copied().map(residue).collect()).collect();
        let point_weights:Vec<Vec<u32>>=ew.iter().map(|w|w[..128].iter().copied().map(residue).collect()).collect();
        let channel_weights:Vec<Vec<u32>>=[&rw,&gw].iter().map(|w|(0..128).map(|i|residue(w.weight_at(i))).collect()).collect();
        let data=format!("{{\\"z\\":{zraw:?},\\"order\\":{:?},\\"inactive\\":{:?},\\"code_weights\\":{code_weights:?},\\"point_weights\\":{point_weights:?},\\"channel_weights\\":{channel_weights:?},\\"source_only\\":true,\\"full_privacy\\":false}}\\n",
            &map.order[..131],map.order[..131].iter().map(|&r|map.inactive[r]).collect::<Vec<_>>());
        std::fs::write(out.join("source-weights.json"),data).unwrap();
''' + anchor)
    anchor = '                for pt in corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap(){'
    assert s.count(anchor) == 1
    s = s.replace(anchor, '''                let points=corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap();
                let mut distinct=std::collections::BTreeSet::new();
                for pt in points{
                    assert_ne!(pt.y,M31::ZERO);
                    assert_eq!(pt.x.mul(pt.x).add(pt.y.mul(pt.y)),M31::ONE);
                    let r=pt.x.mul(pt.x).double().sub(M31::ONE);
                    assert_ne!(r,M31::ONE);assert!(distinct.insert(r.0));''')
    s = s.replace('R119_SOURCE_BOUNDARY', 'R120_SOURCE_BOUNDARY')
    return s
