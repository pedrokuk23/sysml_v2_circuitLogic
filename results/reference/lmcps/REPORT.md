# sysmlc — lmcps_fsm.sysml

Requirements read: 20. Time: 9 s.
Translation coverage: translated assert constraint 1, attribute 81, enum def 2, exhibit state 2, require constraint 20, requirement def 20, transition 12; structural only connect 2, doc 20, end 2, import 1, interface 1, interface def 1, package 1, part 2, part def 3, port 4, port def 2, requirement 1, satisfy 1, subject 20; unsupported none; 216 statements, all matched by the subset grammar.

## Machine `apMachine` (enum ApState)

- Conflicts (contention): 4
  - FSM-002 × FSM-003: [apState=T] good ∧ standby ∧ supported (2 situations, 2 reachable)
  - FSM-004 × FSM-005: [apState=N] standby ∧ ¬good (4 situations, 4 reachable)
  - FSM-006 × FSM-007: [apState=M] good ∧ standby ∧ supported (2 situations, 2 reachable)
  - FSM-008 × FSM-009: [apState=S] apfail ∧ ¬standby (4 situations, 4 reachable)
- Transitions with overlapping guards (where the textual priority matters): none
- Design violates: FSM-003, FSM-004, FSM-007, FSM-008 (reachable: FSM-003, FSM-004, FSM-007, FSM-008)
- Holes per state (one step): T 6/16, N 4/16, M 10/16, S 4/16
- Holes per state (reachable situations only, 56 of 64 situations reachable): T 6, N 4, M 2, S 4

## Machine `senMachine` (enum SenState)

- Conflicts (contention): 1
  - FSM-010 × FSM-011: [senState=Nom] limits ∧ ¬request (2 situations, 1 reachable)
- Transitions with overlapping guards (where the textual priority matters): none
- Design violates: FSM-011 (reachable: FSM-011)
- Holes per state (one step): Nom 2/8, Tr 6/8, F 6/8
- Holes per state (reachable situations only, 16 of 24 situations reachable): Nom 2, Tr 4, F 3

Reachable composite states: 8 of 12.

## Contract `portContract`

- Asserted: `apSide.mode or apSide.request`; projection: `Or(mode, request)`; equivalent: True
- holes_senMachine: 14 → 11

## Parent requirements, one step (z3)

- FSM-001: counterexample

## EDA: Yosys (temporal induction on the sequential circuit)

| Requirement | Result |
|---|---|
| FSM-001 | counterexample |
| FSM-001v2 | counterexample |
| FSM-001v3 | proved (IC3) |
| FSM-002 | proved (k=1) |
| FSM-003 | counterexample |
| FSM-004 | counterexample |
| FSM-005 | proved (k=1) |
| FSM-006 | proved (k=1) |
| FSM-007 | counterexample |
| FSM-008 | counterexample |
| FSM-009 | proved (k=1) |
| FSM-010 | proved (k=1) |
| FSM-011 | counterexample |
| FSM-012 | proved (k=1) |
| FSM-013 | proved (k=1) |

Inductive invariant found by IC3 for FSM-001v3 (lemmas the requirement relies on):

- ¬pre1_notLimits ∨ apState ∈ {T, N} ∨ senState ∈ {Tr}
- apState ∈ {T, M, S} ∨ senState ∈ {Nom, F}
- ¬pre2_notLimits ∨ ¬pre1_autopilot ∨ apState ∈ {T, N}
- ¬pre1_notLimits ∨ senState ∈ {Nom, Tr}
- ¬pre2_notLimits ∨ ¬pre1_autopilot ∨ ¬pre2_autopilot ∨ apState ∈ {N, M, S} ∨ ¬pre3_notLimits
- ¬pre2_notLimits ∨ ¬pre1_limits ∨ ¬pre2_autopilot ∨ ¬pre4_notLimits ∨ senState ∈ {F} ∨ ¬pre3_notLimits ∨ ¬pre3_autopilot

And-inverter graph (AIG), as written → optimized (Yosys synth + freduce/fraig):
- requirements (combinational): 204 AND / 369 NOT → 68 AND / 57 NOT
- design (sequential): 187 AND → 67 AND, 4 flip-flops

## Files

- `view_apMachine.png`
- `view_senMachine.png`
- `view_proofs.png`
