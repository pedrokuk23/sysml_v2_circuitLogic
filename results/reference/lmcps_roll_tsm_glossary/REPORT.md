# sysmlc — lmcps_roll_tsm_glossary.sysml

Requirements read: 9. Time: 0 s.
Translation coverage: translated attribute 26, require constraint 9, requirement def 9; structural only doc 9, import 1, package 1, subject 9; unsupported none; 64 statements, all matched by the subset grammar.

## Output `rollHoldReference` selected by AP-003A, AP-003B, AP-003C, AP-003D

- Conflicts (contention): AP-003B × AP-003D, AP-003C × AP-003D
- Holes: none
- Overlaps: AP-003B & AP-003D, AP-003C & AP-003D
- AP-003A: `Or(30 >= turnKnob, turnKnob >= -30)` is always true
- AP-003D: `Or(30 >= turnKnob, turnKnob >= -30)` is always true

## Output `setVal` selected by TSM-002, TSM-003a, TSM-003b, TSM-003c

- Conflicts (contention): none
- Holes: `And(0 <= ToReal(FC), 7 >= ToReal(FC), noFail == (0 == ToReal(FC)), Not(noFail), Not(1 == ToReal(FC)), Not(2 == ToReal(FC)), Not(4 == ToReal(FC)))`
- Overlaps: none

## Files

