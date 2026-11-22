package TwoMachines {
    private import ScalarValues::*;
    enum def Mode { enum Idle; enum Run; }
    requirement def <'R1'> Start1 {
        subject a;
        in attribute state1 : Mode;
        in attribute go : Boolean;
        out attribute next1 : Mode;
        require constraint { (state1 == Mode::Idle and go) implies next1 == Mode::Run }
    }
    requirement def <'R2'> Start2 {
        subject b;
        in attribute state2 : Mode;
        in attribute go : Boolean;
        out attribute next2 : Mode;
        require constraint { (state2 == Mode::Idle and go) implies next2 == Mode::Run }
    }
    part def A {
        exhibit state m1 {
            entry; then Idle;
            state Idle; state Run;
            transition a1 first Idle if go then Run;
        }
    }
    part def B {
        exhibit state m2 {
            entry; then Idle;
            state Idle; state Run;
            transition b1 first Idle if go then Run;
        }
    }
}
