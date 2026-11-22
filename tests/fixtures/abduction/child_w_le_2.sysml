package AbductionScalar {
    private import ScalarValues::*;
    private import ModelingMetadata::*;
    requirement def <'P'> Parent {
        subject s;
        in attribute w : Real;
        require constraint { w <= 1.0 }
    }
    requirement def <'C'> Child {
        subject s;
        in attribute w : Real;
        require constraint { w <= 2.0 }
    }
    requirement p : Parent;
    requirement c : Child;
    #refinement dependency f from c to p;
}
