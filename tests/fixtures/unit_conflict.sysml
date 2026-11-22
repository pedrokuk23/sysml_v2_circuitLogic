package UnitConflict {
    private import ScalarValues::*;
    requirement def <'GLO-1'> Range {
        subject s;
        out attribute y : Real;
        require constraint { y <= 0.0 }
    }
    requirement def <'R1'> Drive {
        subject s;
        in attribute x : Boolean;
        out attribute y : Real;
        require constraint { x implies y == 1.0 }
    }
}
