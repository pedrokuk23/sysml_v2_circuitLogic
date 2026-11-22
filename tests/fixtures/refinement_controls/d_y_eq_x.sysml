package RefinementControl {
    private import ScalarValues::*;
    private import ModelingMetadata::*;
    requirement def <'GLO-1'> Relation {
        subject s;
        in attribute x : Boolean;
        out attribute y : Boolean;
        require constraint { y == x }
    }
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
        require constraint { y }
    }
    requirement p : Parent;
    requirement c : Child;
    #refinement dependency f from c to p;
}
