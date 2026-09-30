"""Exact source transformation for an extra public annihilator root at x=1."""
def build(s):
    start=s.index('    let cases=[');end=s.index('    let rows=',start)
    s=s[:start]+'''    let cases=[("high_code_support_pivot_check",[1,1,2,3,4,0,2,3,4,2])];
'''+s[end:]
    replacements=[
      ('r118_primal_source.rs','r119_primal_source.rs'),
      ('(0..27).chain([29])','(0..24).chain([26])'),
      ('v[22+c/3]=K::ONE;observe','v[23+c/3]=K::ONE;v[0]=K::ONE.neg();observe'),
      ('let root_independent_precondition=low_nonzero==[0,0,0]&&channel_low==[0,0];',
'''// A low remainder is no longer annihilated automatically: its source
        // observations depend only on the sum of its natural-basis coefficients.
        // Adding x-1 to the root polynomial makes that sum zero. Check the
        // exact low map, not sampled root schedules, before using the section.
        let mut low_column_checks=0;let mut root_independent_precondition=true;
        for slot in 1..4{
            let mut unit=vec![K::ZERO;32];unit[0]=K::ONE;
            let reference=observe(&make_q(&unit,slot));
            for j in 0..23{let mut unit=vec![K::ZERO;32];unit[j]=K::ONE;
                root_independent_precondition &= observe(&make_q(&unit,slot))==reference;low_column_checks+=17;
            }
        }'''),
      ('let mut p=vec![K::ONE];','let mut p=vec![K::ONE.neg(),K::ONE];'),
      ('for i in 1..10','for i in 1..9'),
      ('let d=22+c/3','let d=23+c/3'),
      ('(22..=d)','(23..=d)'),
      ('shifts[top-22]','shifts[top-23]'),
      ('rem[22..]','rem[23..]'),
      ('assert_eq!(observe(&make_q(&v,c%3+1)),os[at]);normalized_checks+=17;',
       'assert_eq!(v.iter().copied().fold(K::ZERO,|a,b|a.add(b)),K::ZERO);assert_eq!(observe(&make_q(&v,c%3+1)),os[at]);normalized_checks+=17;'),
      ('// The same section strategy: root corrections occupy only q[0..88].',
       '// Augmented section: differences from e_d-e_0 occupy q[0..92] and have coefficient sum zero in each selected slot.'),
      ('\\"root_independent_precondition\\":{root_independent_precondition}',
       '\\"root_independent_precondition\\":{root_independent_precondition},\\"low_column_checks\\":{low_column_checks},\\"extra_root_one\\":true'),
      ('R118_SOURCE_BOUNDARY','R119_SOURCE_BOUNDARY')]
    for old,new in replacements:
        assert old in s,old;s=s.replace(old,new)
    return s
