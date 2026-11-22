package RefinementKinds {
    private import ScalarValues::*;
    private import ModelingMetadata::*;
    requirement def <'P'> Parent {
        subject s;
        in attribute x : Boolean;
        out attribute y : Boolean;
        require constraint { y }
    }
    requirement def <'C'> Child {
        subject s;
        in attribute x : Boolean;
        out attribute y : Boolean;
        require constraint { x and y }
    }
    requirement p : Parent;
    requirement c : Child;
    #refinement dependency f from c to p;
}
