from cflibs.inversion.physics.closure import ClosureEquation
from cflibs.inversion.common.strict import require_simplex
import math
# Si, Al, Ca with equal abundance: q_s = log(N_s/U_s) at U=1 -> equal
res = ClosureEquation.apply_oxide_mode({"Si":0.0,"Al":0.0,"Ca":0.0},{"Si":1.0,"Al":1.0,"Ca":1.0},{"Si":2.0,"Al":1.5,"Ca":1.0})
print(res.mode, res.concentrations, "sum=", sum(res.concentrations.values()))
g = require_simplex(list(res.concentrations.values()), strict=False)
print("require_simplex passed:", getattr(g, "passed", g))
