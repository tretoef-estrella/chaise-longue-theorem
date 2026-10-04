# a00_tools.py — pilot, 2 Oct 2026. Which tools exist here (no mathematics).
import flint, numpy, sys
print("python", sys.version.split()[0], "numpy", numpy.__version__, "flint", flint.__version__)
M = flint.nmod_mat(2, 3, [1, 2, 3, 2, 4, 6], 7)
print("nmod_mat rank", M.rank(), "rref", M.rref())
