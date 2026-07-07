---
name: install-project-deps
description: >
  Install or repair dependencies for the P3SAML3P workspace, including the
  project .venv, SAT/Pandas packages, IBM CPLEX Optimization Studio 22.2, and
  the required DOcplex runtime upgrade that removes Community Edition limits.
  Use when setting up the project, fixing ModuleNotFoundError, or debugging
  CPLEX Error 1016 / "Community Edition. Problem size limits exceeded".
---

# Install Project Dependencies

## Required companion skill

Before running Python commands, read and follow `use-project-venv`.

Use this interpreter for P3SAML3P:

```bash
/home/lucifong/P3SAML3P/.venv/bin/python3
```

## Create venv

If `.venv` is missing:

```bash
/usr/bin/python3 -m venv .venv
```

If this fails with `ensurepip is not available`, install venv support:

```bash
sudo apt-get update
sudo apt-get install -y python3.10-venv
/usr/bin/python3 -m venv --clear .venv
```

## Install Python packages

Install the project dependencies with the venv Python:

```bash
/home/lucifong/P3SAML3P/.venv/bin/python3 -m pip install --upgrade pip
/home/lucifong/P3SAML3P/.venv/bin/python3 -m pip install python-sat tabulate pandas openpyxl pypblib docplex cplex
```

Network access to PyPI may require escalation outside the sandbox.

## Install CPLEX Studio 22.2

The educational Linux installer used in this workspace is:

```bash
/home/lucifong/IBM_ILOG_CPLEX_OptStdv22.2_LIN.bin
```

The installer requires Java 11+:

```bash
sudo apt-get install -y openjdk-11-jre-headless
```

Run the installer in console mode and install to the user home directory:

```bash
/home/lucifong/IBM_ILOG_CPLEX_OptStdv22.2_LIN.bin -i console
```

Choose English, accept the license, and use:

```bash
/home/lucifong/CPLEX_Studio222
```

## Important: upgrade DOcplex runtime

CPLEX Optimization Studio 22.2 no longer ships the Python interface inside the
`.bin` tree. `pip install cplex` installs the Community Edition runtime first.
After installing Studio, always run:

```bash
/home/lucifong/P3SAML3P/.venv/bin/docplex config --upgrade /home/lucifong/CPLEX_Studio222
```

This copies the size-unlimited CPLEX runtime from Studio into the venv. Without
this step, DOcplex may fail with:

```text
CPLEX Error 1016: Community Edition. Problem size limits exceeded.
```

## Verify

Check imports:

```bash
/home/lucifong/P3SAML3P/.venv/bin/python3 -c "import pysat; print('pysat OK')"
/home/lucifong/P3SAML3P/.venv/bin/python3 -c "import docplex, cplex; print('docplex', docplex.__version__); print('cplex', cplex.Cplex().get_version())"
/home/lucifong/P3SAML3P/.venv/bin/python3 -m pip check
```

Check that CPLEX is no longer Community-limited by running a model above 1000
constraints:

```bash
cd /home/lucifong/P3SAML3P
/home/lucifong/P3SAML3P/.venv/bin/python3 solvers/CPLEX_ILP.py --test 0 3 10
```

Expected signal: it solves `MERTENS r=3 R=10` without CPLEX Error 1016.
