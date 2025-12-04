# CI/CD Workflows

Three workflows, one proof.

## Workflows

### ci.yml (PRs and main pushes)

**Trigger:** Pull requests to `main` and pushes to `main`

**Jobs:**
1. **agda-verification:** Compile `FirstDistinction.agda` with `--safe --without-K --no-libraries`
2. **validation-tests:** Run `validate_K4.py` and `validate_lambda.py`

### test-ci.yml (non-main branches)

**Trigger:** Push to any branch except `main`

**Steps:**
1. Compile `FirstDistinction.agda` with `--safe --without-K --no-libraries`
2. Check for holes `{!!}`
3. Run `validate_K4.py` (7 numerical tests)

### release-ci.yml (main only)

**Trigger:** Push to `main`

**Steps:**
1. Same verification as test-ci
2. Create GitHub Release with version tag
3. Include source archive

## What Gets Verified

```
FirstDistinction.agda  # Complete proof: D₀ → G_μν = 8T_μν
validate_K4.py         # K₄ eigenvalues, Königsklasse predictions (7 tests)
validate_lambda.py     # Λ-dilution derivation, 10^{-122} problem (7 tests)
```

## Local Testing

```bash
# Agda verification
agda --safe --without-K --no-libraries FirstDistinction.agda

# Numerical validation
python validate_K4.py
python validate_lambda.py
```
