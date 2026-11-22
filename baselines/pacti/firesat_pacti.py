"""Pacti baseline: compute the missing payload specification of the FireSat resolution budget by contract quotient,
and compare with the interpolant interval of the paper. Units: angles in microradians; r = 30 m / h in microradians
(30/700 km = 42.857 urad ... 30/500 km = 60 urad)."""
import json, time
from pacti.contracts import PolyhedralIoContract
t = time.time()
# system: for altitudes in the orbit band, the total blur beta + eps must fit in r = 30/h
system = PolyhedralIoContract.from_strings(
    input_vars=["r"], output_vars=["beta", "eps"],
    assumptions=["-r <= -42.857142857", "r <= 60"],
    guarantees=["beta + eps - r <= 0"])
# attitude control (jitter allocation): eps <= 3 urad, eps >= 0
acs = PolyhedralIoContract.from_strings(
    input_vars=[], output_vars=["eps"], assumptions=[], guarantees=["eps <= 3", "-eps <= 0"])
missing = system.quotient(acs)
# the payload candidate (D >= 0.26 m): beta <= 39.415 urad, beta >= 0
mk = lambda b: PolyhedralIoContract.from_strings(input_vars=["r"], output_vars=["beta"],
        assumptions=["-r <= -42.857142857", "r <= 60"], guarantees=[f"beta <= {b}", "-beta <= 0"])
payload = mk(39.415384615)
res = dict(quotient=str(missing), payload_D026_refines_quotient=payload.refines(missing), seconds=round(time.time() - t, 3))
# a payload at the weakest interpolant (39.857) and slightly above it
for b in (39.857, 39.858, 39.9):
    res[f"payload_beta_le_{b}_refines_quotient"] = mk(b).refines(missing)
print(json.dumps(res, indent=1, default=str)); json.dump(res, open("pacti_results.json", "w"), indent=1, default=str)
