// Lockheed Martin cyber-physical challenges, as formalized by NASA in FRET (caseStudies/LMCPS/LM_requirements.json):
// the roll-hold reference of the inner-loop autopilot (AP-003A..D) and the selected value of the triplex signal
// monitor (TSM-002, TSM-003a..c), written in SysML v2 textual notation by the author from the FRET text.
// Variant with the glossary axiom noFail <=> FC = 0.
// AP-003A..D apply in roll-hold mode, which is the only mode modeled here. Angles in degrees.
package LMCPS_RealValued_Glossary {
    private import ScalarValues::*;

    // ------------------------------------------------------------------ roll-hold reference (AP-003A..D)
    requirement def <'AP-003A'> RollHoldOtherwise {
        subject ap;
        doc /* If none of the conditions of AP-003B, C and D holds, the roll-hold reference is the roll angle. */
        in attribute rollAngle : Real;
        in attribute turnKnob : Real;
        out attribute rollHoldReference : Real;
        require constraint { not ((rollAngle > -6.0 and rollAngle < 6.0) or (rollAngle <= -30.0 or rollAngle >= 30.0)
                                  or ((turnKnob >= 3.0 or turnKnob <= -3.0) and (turnKnob <= 30.0 or turnKnob >= -30.0)))
                             implies rollHoldReference == rollAngle }
    }
    requirement def <'AP-003B'> RollHoldSmall {
        subject ap;
        doc /* Small roll angles: the reference is wings level. */
        in attribute rollAngle : Real;
        out attribute rollHoldReference : Real;
        require constraint { (rollAngle < 6.0 and rollAngle > -6.0) implies rollHoldReference == 0.0 }
    }
    requirement def <'AP-003C'> RollHoldLimit {
        subject ap;
        doc /* Large roll angles: the reference is limited to 30 degrees with the sign of the roll angle. */
        in attribute rollAngle : Real;
        out attribute rollHoldReference : Real;
        require constraint { (-30.0 >= rollAngle or rollAngle >= 30.0)
                             implies rollHoldReference == 30.0 * (if rollAngle >= 0.0 ? 1.0 else -1.0) }
    }
    requirement def <'AP-003D'> RollHoldKnob {
        subject ap;
        doc /* Turn-knob command, "up to a 30 degree limit" in the natural-language text. */
        in attribute turnKnob : Real;
        out attribute rollHoldReference : Real;
        require constraint { ((turnKnob >= 3.0 or turnKnob <= -3.0) and (turnKnob <= 30.0 or turnKnob >= -30.0))
                             implies rollHoldReference == turnKnob }
    }

    // ------------------------------------------------------------------ triplex signal monitor (TSM-002, 003a..c)
    requirement def <'GLO-FC'> FaultCode {
        subject tsm;
        doc /* The fault code is a three-bit word, and zero means no failure (an axiom the FRET set does not state;
               this variant of the model adds it). */
        in attribute FC : Integer;
        in attribute noFail : Boolean;
        require constraint { FC >= 0 and FC <= 7 and (noFail == (FC == 0)) }
    }
    requirement def <'TSM-002'> SelectMid {
        subject tsm;
        doc /* With no failure, the selected value is the middle value of the three signals. */
        in attribute noFail : Boolean;
        in attribute midValue : Real;
        out attribute setVal : Real;
        require constraint { noFail implies setVal == midValue }
    }
    requirement def <'TSM-003a'> SelectAB {
        subject tsm;
        doc /* Fault code 1: average of signals a and b. */
        in attribute FC : Integer;
        in attribute ia : Real;
        in attribute ib : Real;
        out attribute setVal : Real;
        require constraint { FC == 1 implies setVal == 0.5 * (ia + ib) }
    }
    requirement def <'TSM-003b'> SelectAC {
        subject tsm;
        doc /* Fault code 2: average of signals a and c. */
        in attribute FC : Integer;
        in attribute ia : Real;
        in attribute ic : Real;
        out attribute setVal : Real;
        require constraint { FC == 2 implies setVal == 0.5 * (ia + ic) }
    }
    requirement def <'TSM-003c'> SelectBC {
        subject tsm;
        doc /* Fault code 4: average of signals b and c. */
        in attribute FC : Integer;
        in attribute ib : Real;
        in attribute ic : Real;
        out attribute setVal : Real;
        require constraint { FC == 4 implies setVal == 0.5 * (ib + ic) }
    }
}
