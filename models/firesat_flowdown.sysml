// FireSat quantitative flow-down (after SMAD; top-level requirements MR-RES and MR-LOC from the CC0 gist by
// capsulecorplab). First-order nadir physics:
//   resolution  X = h (2.44 lambda / D + eps)   diffraction spot (lambda = 4.2 um) plus line-of-sight jitter
//   location    L = h thetaK + dr              attitude-knowledge error projected on ground plus orbit error
// The child requirements are an ILLUSTRATIVE allocation written by us. ADCS-1 allocates 5 urad of jitter,
// which misses the resolution budget; ADCS-1R is its revision to 3 urad. ORB-GEO is the geostationary concept. Units: m, rad.
// Flow-downs are #refinement dependencies (ModelingMetadata): the derived requirements (sources) refine the mission
// requirement (target), i.e. together with the physics they are meant to be sufficient for it, which the compiler checks.
package FireSatFlowdown {
    private import ScalarValues::*;
    private import ModelingMetadata::*;

    part def Payload { attribute D : Real; attribute blur : Real; }
    part def Adcs { attribute eps : Real; attribute thetaK : Real; }
    part def Orbit { attribute h : Real; }
    part def Nav { attribute dr : Real; }

    // ------------------------------------------------------------------ physics of each subsystem (glossary axioms)
    requirement def <'GLO-PAY'> PayloadOptics {
        subject pay : Payload;
        doc /* Diffraction-limited blur of the infrared payload, as an angle: 2.44 lambda / D. */
        require constraint { pay.D > 0 and pay.blur == 2.44 * 0.0000042 / pay.D }
    }
    requirement def <'GLO-ADCS'> AdcsQuantities {
        subject adcs : Adcs;
        doc /* Jitter and attitude-knowledge error are non-negative angles. */
        require constraint { adcs.eps >= 0 and adcs.thetaK >= 0 }
    }
    requirement def <'GLO-ORB'> OrbitQuantities {
        subject orb : Orbit;
        doc /* Orbit altitude above the surface. */
        require constraint { orb.h > 0 }
    }
    requirement def <'GLO-NAV'> NavQuantities {
        subject nav : Nav;
        doc /* Orbit position error is non-negative. */
        require constraint { nav.dr >= 0 }
    }

    requirement def <'GLO-SYS'> SystemPhysics {
        subject sys : FlowdownSystem;
        doc /* First-order nadir physics: X = h (blur + eps) and L = h thetaK + dr. */
        require constraint { sys.X == sys.orbit.h * (sys.payload.blur + sys.adcs.eps) and
                             sys.L == sys.orbit.h * sys.adcs.thetaK + sys.nav.dr }
    }

    // ------------------------------------------------------------------ parents (mission requirements)
    requirement def <'MR-RES'> Resolution {
        subject sys : FlowdownSystem;
        doc /* 30 m resolution at nadir. */
        require constraint { sys.X <= 30 }
    }
    requirement def <'MR-LOC'> Location {
        subject sys : FlowdownSystem;
        doc /* 500 m location accuracy at nadir. */
        require constraint { sys.L <= 500 }
    }

    // ------------------------------------------------------------------ children (illustrative allocation)
    requirement def <'ORB-1'> OrbitBand {
        subject orb : Orbit;
        doc /* Low Earth orbit between 500 km and 700 km. */
        require constraint { orb.h >= 500000 and orb.h <= 700000 }
    }
    requirement def <'ORB-GEO'> GeostationaryOrbit {
        subject orb : Orbit;
        doc /* Geostationary concept. */
        require constraint { orb.h == 35786000 }
    }
    requirement def <'PAY-2'> Aperture {
        subject pay : Payload;
        doc /* Aperture of at least 0.26 m. */
        require constraint { pay.D >= 0.26 }
    }
    requirement def <'ADCS-1'> Jitter {
        subject adcs : Adcs;
        doc /* Line-of-sight jitter during integration of at most 5 urad. */
        require constraint { adcs.eps <= 0.000005 }
    }
    requirement def <'ADCS-1R'> JitterRevised {
        subject adcs : Adcs;
        doc /* Revised jitter allocation: at most 3 urad. */
        require constraint { adcs.eps <= 0.000003 }
    }
    requirement def <'ADCS-2'> Knowledge {
        subject adcs : Adcs;
        doc /* Attitude knowledge better than 0.03 deg. */
        require constraint { adcs.thetaK <= 0.0005236 }
    }
    requirement def <'NAV-1'> Position {
        subject nav : Nav;
        doc /* Orbit position error of at most 100 m. */
        require constraint { nav.dr <= 100 }
    }

    // ------------------------------------------------------------------ system and derivations
    part def FlowdownSystem {
        part payload : Payload;
        part adcs : Adcs;
        part orbit : Orbit;
        part nav : Nav;
        attribute X : Real;      // ground resolution [m]
        attribute L : Real;      // location error [m]
    }
    part flowdown : FlowdownSystem;
    satisfy res by flowdown;
    satisfy loc by flowdown;

    requirement res : Resolution;
    requirement loc : Location;
    requirement orb1 : OrbitBand;
    requirement orbGeo : GeostationaryOrbit;
    requirement pay2 : Aperture;
    requirement adcs1 : Jitter;
    requirement adcs1r : JitterRevised;
    requirement adcs2 : Knowledge;
    requirement nav1 : Position;

    #refinement dependency resFlow from orb1, pay2, adcs1 to res;
    #refinement dependency resFlowRevised from orb1, pay2, adcs1r to res;
    #refinement dependency locFlow from orb1, adcs2, nav1 to loc;
    #refinement dependency geoFlow from orbGeo, pay2, adcs1r to res;
}
