// FireSat (after SMAD; top-level requirements and the two concept options from the CC0 gist by capsulecorplab)
// in SysML v2 textual notation: variability, mission action flow and functional allocation.
// Parameter values are ILLUSTRATIVE (ours), not SMAD's. Units: m, rad, kg, min, % of CPU.
package FireSat {
    private import ScalarValues::*;

    // ------------------------------------------------------------------ top-level requirements (gist)
    requirement def <'MR-RES'> Resolution {
        subject sys : FireSatSystem;
        doc /* 30 m resolution at nadir. Physics (first order): X = h (2.44 lambda/D + eps), with the
               diffraction-limited spot (2.44 lambda/D, lambda = 4.2 um) and the line-of-sight jitter during the
               integration time eps = 3 urad (allocated to attitude control). Off-nadir viewing is not modeled. */
        require constraint { sys.orbit.h * (2.44 * 0.0000042 / sys.payload.D + 0.000003) <= 30 }
    }
    requirement def <'MR-TL'> TimeLate {
        subject sys : FireSatSystem;
        doc /* Send registered mission data within 30 min to up to 50 users. Time late = storage delay + processing. */
        require constraint { sys.storeDelay + sys.procTime <= 30 }
    }
    requirement def <'MR-MASS'> PayloadFitsBus {
        subject sys : FireSatSystem;
        doc /* The payload mass shall not exceed the bus payload capacity. */
        require constraint { sys.payload.mass <= sys.bus.payloadCapacity }
    }

    // ------------------------------------------------------------------ variability (the gist's concept options, factored)
    part def Payload { attribute D : Real; attribute mass : Real; }
    variation part def PayloadChoice :> Payload {
        variant part smallIR : Payload { attribute redefines D = 0.26; attribute redefines mass = 30; }
        variant part largeIR : Payload { attribute redefines D = 1.5;  attribute redefines mass = 400; }
    }
    part def Orbit { attribute h : Real; attribute period : Real; attribute nSat : Integer; }
    variation part def OrbitChoice :> Orbit {
        variant part leo2 : Orbit { attribute redefines h = 700000;   attribute redefines period = 99;   attribute redefines nSat = 2; }
        variant part geo1 : Orbit { attribute redefines h = 35786000; attribute redefines period = 1436; attribute redefines nSat = 1; }
    }
    part def Bus { attribute payloadCapacity : Real; attribute cpuCapacity : Real; }
    variation part def BusChoice :> Bus {
        variant part smallBus : Bus { attribute redefines payloadCapacity = 100; attribute redefines cpuCapacity = 80; }
        variant part midBus   : Bus { attribute redefines payloadCapacity = 500; attribute redefines cpuCapacity = 150; }
    }
    part def Ground { attribute maxGap : Real; }               // worst-case gap between ground contacts [min]
    variation part def GroundChoice :> Ground {
        variant part gs4 : Ground { attribute redefines maxGap = 100; }    // four mid-latitude stations
        variant part gs12 : Ground { attribute redefines maxGap = 20; }    // twelve stations incl. polar sites
    }
    part def Comm { attribute relay : Boolean; }
    variation part def CommChoice :> Comm {
        variant part direct : Comm { attribute redefines relay = false; }
        variant part relayLink : Comm { attribute redefines relay = true; }
    }

    // ------------------------------------------------------------------ mission action flow (one detection cycle)
    action def DetectAndReport {
        in attribute fire : Boolean;
        in attribute linkUp : Boolean;
        in attribute backlog : Boolean;
        first start;
        then action observe { attribute duration : Real = 1; }
        then action detect { attribute duration : Real = 2; attribute cpuLoad : Real = 40; }
        then decide fireCheck;
            if fire then geolocate;
            if not fire then done;
        action geolocate { attribute duration : Real = 1; attribute cpuLoad : Real = 30; }
        then fork split;
            then retryMerge;
            then archive;
        merge retryMerge;
        then action downlink { attribute duration : Real = 1; attribute cpuLoad : Real = 20; attribute fixedOnBoard : Real = 1; }
        then decide linkCheck;
            if linkUp then sync;
            if linkUp and backlog then retry;
        action retry { attribute duration : Real = 3; }
        then retryMerge;
        action archive { attribute duration : Real = 1; }
        then sync;
        join sync;
        then action notify { attribute duration : Real = 1; }
        then done;
    }

    requirement res : Resolution;
    requirement tl : TimeLate;
    requirement mass : PayloadFitsBus;

    // ------------------------------------------------------------------ architecture and allocation
    part def FireSatSystem {
        part payload : PayloadChoice;
        part orbit : OrbitChoice;
        part bus : BusChoice;
        part ground : GroundChoice;
        part comm : CommChoice;
        part obc;                 // on-board computer (capacity = bus.cpuCapacity)
        part groundProc;          // ground processing (unbounded capacity)
        perform action mission : DetectAndReport;
        allocate mission.detect to obc;
        allocate mission.geolocate to obc;
        allocate mission.downlink to obc;
        // timing model: storage delay is ~2 min with relay or continuous view (GEO), else the worst-case contact gap;
        // processing time is 5 min if detection runs on board, 15 min on the ground.
        attribute detectOnBoard : Boolean;     // allocation indicator of 'detect' (decided by the analysis)
        attribute storeDelay : Real = if comm.relay or orbit.nSat == 1 ? 2 else ground.maxGap;
        attribute procTime : Real = if detectOnBoard ? 5 else 15;
    }
    part fireSat : FireSatSystem;
    satisfy res by fireSat;
    satisfy tl by fireSat;
    satisfy mass by fireSat;
}
