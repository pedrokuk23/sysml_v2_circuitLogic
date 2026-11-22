// LMCPS "Finite State Machine" challenge (Lockheed Martin / NASA FRET case study) in SysML v2 textual notation.
// Requirements are written as SysML v2 requirement definitions whose 'require constraint' is a Boolean
// expression in the KerML expression language: the logic IS the requirement; the doc keeps the original text.
// Convention for one-step requirements: 'state' = current state, 'nextState' = state at the next step.
package LMCPS_FSM {
    private import ScalarValues::*;

    enum def ApState { enum T; enum N; enum M; enum S; }      // TRANSITION, NOMINAL, MANEUVER, STANDBY
    enum def SenState { enum Nom; enum Tr; enum F; }          // NOMINAL, TRANSITION, FAULT

    // ------------------------------------------------------------------ interface
    port def ApToSensor {
        out attribute mode : Boolean;       // autopilot not in TRANSITION
        out attribute request : Boolean;    // autopilot in TRANSITION or NOMINAL
    }
    port def SensorToAp {
        out attribute good : Boolean;       // sensor not in FAULT
    }
    interface def ApSensorLink {
        end apSide : ApToSensor;
        end senSide : ~ApToSensor;
        // Port contract: synthesized by projection (strongest Craig interpolant) of the autopilot's output map
        // onto the port signals. The sensor may rely on it; its violating input combinations become don't cares.
        assert constraint portContract { apSide.mode or apSide.request }
    }

    // ------------------------------------------------------------------ glossary axioms (data dictionary made formal)
    requirement def <'GLO-1'> PullupMeaning {
        subject fsm;
        doc /* pullup: True when the autopilot is in the MANEUVER state (variable table, not a requirement). */
        in attribute nextState : ApState;
        out attribute pullup : Boolean;
        require constraint { pullup == (nextState == ApState::M) }
    }
    requirement def <'GLO-2'> PortMeaning {
        subject fsm;
        doc /* MODE: not in transition; REQUEST: transition to nominal operation (variable table). */
        in attribute nextState : ApState;
        out attribute mode : Boolean;
        out attribute request : Boolean;
        require constraint { mode == (nextState != ApState::T) and
                             request == (nextState == ApState::T or nextState == ApState::N) }
    }

    requirement def <'GLO-3'> GoodMeaning {
        subject fsm;
        doc /* good: false indicates an unsafe situation (sensor output; the autopilot reads its previous value). */
        in attribute senState : SenState;
        out attribute good : Boolean;
        require constraint { good == (senState != SenState::F) }
    }
    requirement def <'GLO-4'> AutopilotMeaning {
        subject fsm;
        doc /* autopilot = (not standby) and supported and (not apfail)  (FRET variable definition). */
        in attribute standby : Boolean; in attribute supported : Boolean; in attribute apfail : Boolean;
        out attribute autopilot : Boolean;
        require constraint { autopilot == (not standby and supported and not apfail) }
    }
    requirement def <'GLO-5'> NotLimits {
        subject fsm;
        doc /* auxiliary signal, so that its delayed copies start false as FRET's preBool(false, ...). */
        in attribute limits : Boolean;
        out attribute notLimits : Boolean;
        require constraint { notLimits == (not limits) }
    }

    // ------------------------------------------------------------------ parent requirement
    requirement def <'FSM-001'> LatchPullup {
        subject fsm;
        doc /* Exceeding sensor limits shall latch an autopilot pullup when the pilot is not in control
               (not standby) and the system is supported without failures (not apfail). */
        in attribute limits : Boolean;
        in attribute standby : Boolean;
        in attribute apfail : Boolean;
        in attribute supported : Boolean;
        out attribute pullup : Boolean;
        require constraint { (limits and not standby and not apfail and supported) implies pullup }
    }

    // Temporal versions (FRET history of FSM-001). Compiler convention: preK_x = x delayed K steps, initially false.
    requirement def <'FSM-001v2'> LatchPullupV2 {
        subject fsm;
        doc /* if autopilot & pre_autopilot & pre_limits FSM shall immediately satisfy pullup. */
        in attribute autopilot : Boolean; in attribute pre1_autopilot : Boolean; in attribute pre1_limits : Boolean;
        out attribute pullup : Boolean;
        require constraint { (autopilot and pre1_autopilot and pre1_limits) implies pullup }
    }
    requirement def <'FSM-001v3'> LatchPullupV3 {
        subject fsm;
        doc /* if persisted(3, autopilot) & persisted(3, preBool(false, preBool(false, !limits))) & preBool(false, limits)
               FSM shall immediately satisfy pullup. */
        in attribute autopilot : Boolean; in attribute pre1_autopilot : Boolean; in attribute pre2_autopilot : Boolean;
        in attribute pre3_autopilot : Boolean; in attribute pre2_notLimits : Boolean; in attribute pre3_notLimits : Boolean;
        in attribute pre4_notLimits : Boolean; in attribute pre5_notLimits : Boolean; in attribute pre1_limits : Boolean;
        out attribute pullup : Boolean;
        require constraint { (autopilot and pre1_autopilot and pre2_autopilot and pre3_autopilot and pre2_notLimits and
                              pre3_notLimits and pre4_notLimits and pre5_notLimits and pre1_limits) implies pullup }
    }

    // ------------------------------------------------------------------ autopilot requirements (original versions)
    requirement def <'FSM-002'> ApTtoS {
        subject fsm;
        doc /* The autopilot shall change states from TRANSITION to STANDBY when the pilot is in control (standby). */
        in attribute apState : ApState; in attribute standby : Boolean; out attribute nextState : ApState;
        require constraint { (apState == ApState::T and standby) implies nextState == ApState::S }
    }
    requirement def <'FSM-003'> ApTtoN {
        subject fsm;
        doc /* The autopilot shall change states from TRANSITION to NOMINAL when the system is supported and sensor data is good. */
        in attribute apState : ApState; in attribute good : Boolean; in attribute supported : Boolean;
        out attribute nextState : ApState;
        require constraint { (apState == ApState::T and good and supported) implies nextState == ApState::N }
    }
    requirement def <'FSM-004'> ApNtoM {
        subject fsm;
        doc /* The autopilot shall change states from NOMINAL to MANEUVER when the sensor data is not good. */
        in attribute apState : ApState; in attribute good : Boolean; out attribute nextState : ApState;
        require constraint { (apState == ApState::N and not good) implies nextState == ApState::M }
    }
    requirement def <'FSM-005'> ApNtoS {
        subject fsm;
        doc /* The autopilot shall change states from NOMINAL to STANDBY when the pilot is in control (standby). */
        in attribute apState : ApState; in attribute standby : Boolean; out attribute nextState : ApState;
        require constraint { (apState == ApState::N and standby) implies nextState == ApState::S }
    }
    requirement def <'FSM-006'> ApMtoS {
        subject fsm;
        doc /* The autopilot shall change states from MANEUVER to STANDBY when the pilot is in control (standby) and sensor data is good. */
        in attribute apState : ApState; in attribute standby : Boolean; in attribute good : Boolean;
        out attribute nextState : ApState;
        require constraint { (apState == ApState::M and standby and good) implies nextState == ApState::S }
    }
    requirement def <'FSM-007'> ApMtoT {
        subject fsm;
        doc /* The autopilot shall change states from PULLUP to TRANSITION when the system is supported and sensor data is good. */
        in attribute apState : ApState; in attribute supported : Boolean; in attribute good : Boolean;
        out attribute nextState : ApState;
        require constraint { (apState == ApState::M and supported and good) implies nextState == ApState::T }
    }
    requirement def <'FSM-008'> ApStoT {
        subject fsm;
        doc /* The autopilot shall change states from STANDBY to TRANSITION when the pilot is not in control (not standby). */
        in attribute apState : ApState; in attribute standby : Boolean; out attribute nextState : ApState;
        require constraint { (apState == ApState::S and not standby) implies nextState == ApState::T }
    }
    requirement def <'FSM-009'> ApStoM {
        subject fsm;
        doc /* The autopilot shall change states from STANDBY to MANEUVER when a failure occurs (apfail). */
        in attribute apState : ApState; in attribute apfail : Boolean; out attribute nextState : ApState;
        require constraint { (apState == ApState::S and apfail) implies nextState == ApState::M }
    }

    // ------------------------------------------------------------------ sensor requirements (original versions)
    requirement def <'FSM-010'> SenNtoF {
        subject fsm;
        doc /* The sensor shall change states from NOMINAL to FAULT when limits are exceeded. */
        in attribute senState : SenState; in attribute limits : Boolean; out attribute nextSenState : SenState;
        require constraint { (senState == SenState::Nom and limits) implies nextSenState == SenState::F }
    }
    requirement def <'FSM-011'> SenNtoT {
        subject fsm;
        doc /* The sensor shall change states from NOMINAL to TRANSITION when the autopilot is not requesting support (not request). */
        in attribute senState : SenState; in attribute request : Boolean; out attribute nextSenState : SenState;
        require constraint { (senState == SenState::Nom and not request) implies nextSenState == SenState::Tr }
    }
    requirement def <'FSM-012'> SenFtoT {
        subject fsm;
        doc /* The sensor shall change states from FAULT to TRANSITION when the autopilot is not requesting support (not request) and limits are not exceeded (not limits). */
        in attribute senState : SenState; in attribute request : Boolean; in attribute limits : Boolean;
        out attribute nextSenState : SenState;
        require constraint { (senState == SenState::F and not request and not limits) implies nextSenState == SenState::Tr }
    }
    requirement def <'FSM-013'> SenTtoN {
        subject fsm;
        doc /* The sensor shall change states from TRANSITION to NOMINAL when the autopilot is requesting support (request) and the autopilot reports the correct active mode (mode). */
        in attribute senState : SenState; in attribute request : Boolean; in attribute mode : Boolean;
        out attribute nextSenState : SenState;
        require constraint { (senState == SenState::Tr and request and mode) implies nextSenState == SenState::Nom }
    }

    requirement fsm001 : LatchPullup;

    // ------------------------------------------------------------------ design: parts with state machines
    part def Autopilot {
        in attribute standby : Boolean;
        in attribute apfail : Boolean;
        in attribute supported : Boolean;
        port toSensor : ApToSensor;
        port fromSensor : ~SensorToAp;
        attribute pullup : Boolean;
        exhibit state apMachine {
            entry; then T;
            state T; state N; state M; state S;
            transition t02 first T if standby then S;
            transition t03 first T if fromSensor.good and supported and not standby then N;
            transition t05 first N if standby then S;
            transition t04 first N if not fromSensor.good and not standby then M;
            transition t06 first M if standby and fromSensor.good then S;
            transition t07 first M if supported and fromSensor.good and not standby then T;
            transition t09 first S if apfail then M;
            transition t08 first S if not standby and not apfail then T;
        }
    }
    part def Sensor {
        in attribute limits : Boolean;
        port fromAp : ~ApToSensor;
        port toAp : SensorToAp;
        exhibit state senMachine {
            entry; then Nom;
            state Nom; state Tr; state F;
            transition s10 first Nom if limits then F;
            transition s11 first Nom if not fromAp.request and not limits then Tr;
            transition s12 first F if not fromAp.request or not limits then Tr;
            transition s13 first Tr if fromAp.request and fromAp.mode then Nom;
        }
    }
    part def FSM {
        part autopilot : Autopilot;
        part sensor : Sensor;
        interface link : ApSensorLink connect autopilot.toSensor to sensor.fromAp;
        connect sensor.toAp to autopilot.fromSensor;
        satisfy fsm001 by self;
    }
}
