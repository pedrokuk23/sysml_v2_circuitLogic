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
    part def A {
        exhibit state m1 {
            entry; then Idle;
            state Idle; state Run;
            transition a1 first Idle if go then Run;
        }
    }
}
