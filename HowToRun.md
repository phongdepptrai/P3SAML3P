source .venv/bin/activate
python run_launcher.py
cd /home/phongdeptrai/P3SAML3P && .venv/bin/python compare_solvers.py --csvs Output/Incremental/summary.csv Output/IncrementalSM/summary.csv && echo "RUN SUCCESSFUL"

