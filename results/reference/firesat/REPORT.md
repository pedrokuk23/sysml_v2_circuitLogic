# sysmlc — firesat.sysml

Requirements read: 3. Time: 5 s.
Translation coverage: translated action def 1, allocate 3, attribute 44, decide 2, fork 1, join 1, merge 1, require constraint 3, requirement def 3, variant part 10, variation part def 5; structural only doc 3, import 1, package 1, part 8, part def 6, perform action 1, requirement 3, satisfy 3, subject 3; unsupported none; 120 statements, all matched by the subset grammar.

## Variability

- Valid configurations: 9 of 32
- Eliminated by each requirement alone: {'MR-TL': 4, 'MR-RES': 16, 'MR-MASS': 8}
- Invalid configurations attributed by unsatisfiable core: {'MR-TL': 3, 'MR-RES': 12, 'MR-MASS': 8}
- Dead: ['orbit.geo1'] ({'orbit.geo1': ['MR-RES']})
- Core: ['orbit.leo2']
- Revive orbit.geo1 / MR-RES: impossible — `1281/125000000/payload.D <= -38679/17893000000`
- Declared allocation infeasible in 3 of 9 valid configurations
- Yosys (SAT) proved: core:orbit.leo2, dead:orbit.geo1
- Configuration circuit (AIG): 9 AND as written → 9 AND optimized

## Actions `DetectAndReport`

- fireCheck: complete=True overlaps=[]
- linkCheck: complete=False overlaps=[['sync', 'retry']]
- Deadlocks: 2 valuations; possible loops: 1

## Files

- `view_variability.png`
- `view_allocation.png`
- `view_actions_DetectAndReport.png`
