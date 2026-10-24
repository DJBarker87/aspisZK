fn semantic_boundary(polynomial: &[QM31; 28]) -> QM31 {
    let mut boundary = polynomial[0];
    let mut index = 0usize;
    while index < 28 {
        boundary = QM31::add(boundary, polynomial[index]);
        index += 1;
    }
    boundary
}
