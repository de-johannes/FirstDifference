# CI/CD Workflows

Two workflows, one proof.

## Workflows

### test-ci.yml (non-main branches)

**Trigger:** Push to any branch except `main`

**Steps:**
1. Compile `DRIFE.agda` with `--safe --without-K --no-libraries`
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
DRIFE.agda      # Complete proof: D₀ → G_μν = 8T_μν
validate_K4.py  # K₄ eigenvalues, Königsklasse predictions
```

## Local Testing

```bash
# Agda verification
agda --safe --without-K --no-libraries DRIFE.agda

# Numerical validation
python validate_K4.py
```
