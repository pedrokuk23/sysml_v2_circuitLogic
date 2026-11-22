# sysmlc — firesat_flowdown.sysml

Requirements read: 14. Time: 43 s.
Translation coverage: translated #refinement dependency 4, attribute 8, require constraint 14, requirement def 14; structural only doc 14, import 2, package 1, part 5, part def 5, requirement 9, satisfy 2, subject 14; unsupported none; 92 statements, all matched by the subset grammar.

## Refinement `resFlow`: MR-RES ⇐ ORB-1, PAY-2, ADCS-1

- Implication: fails; worst case of h*((61/25*21/5000000)/D + eps): 31.0908
- Kind: static; children jointly satisfiable: True; static refinement: False; input-total: not applicable (no output attributes declared) (None = inconclusive: the solver answered UNKNOWN)
- Replace ORB-1 (over h): `And(Or(h <= 0, h <= 7864320/11),
    Or(h <= 0,
       h <= 20100475060155015498810/28115020263762707),
    Or(h <= 0,
       h <=
       6532654394550380037113250000000/9137393590836532401675889),
    Or(h <= 0,
       h <=
       2123112678228873512061806250000000000000/2969656818688936317743999440604603),
    Or(h <= 0, h <= 687194767360/961199),
    Or(h <= 0, h <= 2061584302080/3052201),
    Or(h <= 0, h <= 1950000000/2887))` [quantifier elimination; exists]
- Replace PAY-2 (over D): `Or(D <= 0, 1281/125000000/D <= 53/1400000)` [quantifier elimination; exists]
- Replace ADCS-1 (over eps): `eps <= 783/227500000` [quantifier elimination; exists]
- Replace ORB-1 + PAY-2 (over D, h): `Or(D <= 0, h <= 0, h*(1/200000 + 1281/125000000/D) <= 30)` [quantifier elimination; exists]
- Replace ORB-1 + ADCS-1 (over eps, h): `Or(h*(1281/32500000 + eps) <= 30, Not(eps >= 0), h <= 0)` [quantifier elimination; exists]
- Replace PAY-2 + ADCS-1 (over D, eps): `And(Or(D <= 0,
       308094151366691831/440134816338*(1281/125000000/D) +
       308094151366691831/440134816338*eps <=
       30,
       Not(eps >= 0)),
    Or(D <= 0,
       Not(eps >= 0),
       700000*(1281/125000000/D) + 700000*eps <= 30))` [quantifier elimination; exists]
- Interface Adcs (shared eps): none, no interface contract exists: the subsystem's requirements and the rest of the allocation admit a violation of the parent
- Interface Orbit (shared h): none, no interface contract exists: the subsystem's requirements and the rest of the allocation admit a violation of the parent
- Interface Payload (shared blur): none, no interface contract exists: the subsystem's requirements and the rest of the allocation admit a violation of the parent
- Discretisation: 22 of 32 combinations of a0: 500000 <= h, a1: 700000 >= h, a2: 13/50 <= D, a3: 1/200000 >= eps, a4: 30 >= h*((61/25*21/5000000)/D + eps) are feasible; lemmas (a0 | a1) & (a1 | a2 | a3 | ~a4) & (a0 | a4 | ~a2 | ~a3)

## Refinement `resFlowRevised`: MR-RES ⇐ ORB-1, PAY-2, ADCS-1R

- Implication: valid; worst case of h*((61/25*21/5000000)/D + eps): 29.6908
- Kind: static; children jointly satisfiable: True; static refinement: True; input-total: not applicable (no output attributes declared) (None = inconclusive: the solver answered UNKNOWN)
- Replace ORB-1 (over h): `h <= 707290` [numerical (bisection; quantifier elimination exceeded the time limit); exists]
- Replace PAY-2 (over D): `Or(D <= 0, 1281/125000000/D <= 279/7000000)` [quantifier elimination; exists]
- Replace ADCS-1R (over eps): `eps <= 783/227500000` [quantifier elimination; exists]
- Replace ORB-1 + PAY-2 (over D, h): `Or(h*(3/1000000 + 1281/125000000/D) <= 30, h <= 0, D <= 0)` [quantifier elimination; exists]
- Replace ORB-1 + ADCS-1R (over eps, h): `Or(Not(eps >= 0), h*(1281/32500000 + eps) <= 30, h <= 0)` [quantifier elimination; exists]
- Replace PAY-2 + ADCS-1R (over D, eps): `Or(Not(eps >= 0),
   D <= 0,
   700000*(1281/125000000/D) + 700000*eps <= 30)` [quantifier elimination; exists]
- Interface Adcs (shared eps): guarantees ≤ 3.00019e-06, tolerated ≤ 3.44176e-06, margin 4.416e-07
- Interface Orbit (shared h): guarantees ≤ 700000, tolerated ≤ 707291, margin 7291
- Interface Payload (shared blur): guarantees ≤ 3.94158e-05, tolerated ≤ 3.98571e-05, margin 4.413e-07
- Discretisation: 22 of 32 combinations of a0: 500000 <= h, a1: 700000 >= h, a2: 13/50 <= D, a3: 3/1000000 >= eps, a4: 30 >= h*((61/25*21/5000000)/D + eps) are feasible; lemmas (a0 | a1) & (a4 | ~a1 | ~a2 | ~a3)

## Refinement `locFlow`: MR-LOC ⇐ ORB-1, ADCS-2, NAV-1

- Implication: valid; worst case of h*thetaK + dr: 466.52
- Kind: static; children jointly satisfiable: True; static refinement: True; input-total: not applicable (no output attributes declared) (None = inconclusive: the solver answered UNKNOWN)
- Replace ORB-1 (over h): `Or(h <= 1000000000/1309, h <= 0)` [quantifier elimination; exists]
- Replace ADCS-2 (over thetaK): `Or(thetaK <= 1/1750, Not(thetaK >= 0))` [quantifier elimination; exists]
- Replace NAV-1 (over dr): `Or(dr <= 3337/25, Not(dr >= 0))` [quantifier elimination; exists]
- Replace ORB-1 + ADCS-2 (over h, thetaK): `Or(h <= 0, h*thetaK <= 400)` [quantifier elimination; exists]
- Replace ORB-1 + NAV-1 (over dr, h): `And(Or(Not(dr >= 0), h <= 0, -500 <= -1*dr + -1/2048*h),
    Or(Not(dr >= 0),
       h <= 0,
       -500 <= -1*dr + -1309/2500000*h))` [quantifier elimination; exists]
- Replace ADCS-2 + NAV-1 (over dr, thetaK): `And(Or(Not(dr >= 0),
       Not(thetaK >= 0),
       -500 <= -500001*thetaK + -1*dr),
    Or(Not(dr >= 0),
       Not(thetaK >= 0),
       -500 <= -700000*thetaK + -1*dr))` [quantifier elimination; exists]
- Interface Adcs (shared thetaK): guarantees ≤ 0.0005236, tolerated ≤ 0.000571429, margin 4.783e-05
- Interface Nav (shared dr): guarantees ≤ 100, tolerated ≤ 133.48, margin 33.48
- Interface Orbit (shared h): guarantees ≤ 700000, tolerated ≤ 763942, margin 6.394e+04
- Discretisation: 22 of 32 combinations of a0: 500000 <= h, a1: 700000 >= h, a2: 1309/2500000 >= thetaK, a3: 100 >= dr, a4: 500 >= h*thetaK + dr are feasible; lemmas (a0 | a1) & (a4 | ~a1 | ~a2 | ~a3)

## Refinement `geoFlow`: MR-RES ⇐ ORB-GEO, PAY-2, ADCS-1R

- Implication: fails; worst case of h*((61/25*21/5000000)/D + eps): 1517.88
- Kind: static; children jointly satisfiable: True; static refinement: False; input-total: not applicable (no output attributes declared) (None = inconclusive: the solver answered UNKNOWN)
- Replace ORB-GEO (over h): `And(Or(h <= 0, h <= 5242880/7),
    Or(h <= 0, h <= 2977847967734612974030/3975861198663081),
    Or(h <= 0,
       h <=
       74446199193365324350750000000/99396660558325627241199),
    Or(h <= 0,
       h <=
       1861154979834133108768750000000000000/2484919778756145173725577460921),
    Or(h <= 0, h <= 1030792151040/1457381),
    Or(h <= 0, h <= 650000000/919))` [quantifier elimination; exists]
- Replace PAY-2 (over D): `D <= 0` [quantifier elimination; none exists]
- Replace ADCS-1R (over eps): `Not(eps >= 0)` [quantifier elimination; none exists]
- Replace ORB-GEO + PAY-2 (over D, h): `Or(h <= 0, D <= 0, h*(3/1000000 + 1281/125000000/D) <= 30)` [quantifier elimination; exists]
- Replace ORB-GEO + ADCS-1R (over eps, h): `Or(Not(eps >= 0), h <= 0, h*(1281/32500000 + eps) <= 30)` [quantifier elimination; exists]
- Replace PAY-2 + ADCS-1R (over D, eps): `Or(-3 <= -3578600*eps + -3578600*(1281/125000000/D),
   Not(eps >= 0),
   D <= 0)` [quantifier elimination; exists]
- Interface Adcs (shared eps): none, no interface contract exists: the subsystem's requirements and the rest of the allocation admit a violation of the parent
- Interface Orbit (shared h): none, no interface contract exists: the subsystem's requirements and the rest of the allocation admit a violation of the parent
- Interface Payload (shared blur): none, no interface contract exists: the subsystem's requirements and the rest of the allocation admit a violation of the parent
- Discretisation: 13 of 16 combinations of a0: 35786000 == h, a1: 13/50 <= D, a2: 3/1000000 >= eps, a3: 30 >= h*((61/25*21/5000000)/D + eps) are feasible; lemmas (a1 | ~a0 | ~a3) & (a2 | ~a0 | ~a3)

## Files

