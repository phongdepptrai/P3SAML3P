# Run Notes

- All solver batch runs are currently capped at `r_max = 2` for testing.
- To run `r_max = 3` again, edit `BATCH_R_MAX_LIMIT` in the solver file.
- Solver timeouts are currently `3600` seconds.
- `solvers/CPLEX_msls.py` is intentionally left at `600` seconds.
