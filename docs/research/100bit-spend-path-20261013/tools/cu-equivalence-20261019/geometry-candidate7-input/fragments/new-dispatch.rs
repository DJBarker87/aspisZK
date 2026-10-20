        let z=geometry.line_z[i-geometry.start];
        accumulate_with_node(p,a,z.mul(z).double().sub(M31::ONE),folded);
