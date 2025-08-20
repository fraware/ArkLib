# GitHub Repository Security Configuration Guide

## Branch Protection Rules

### Main Branch Protection
1. Go to **Settings** → **Branches**
2. Click **Add rule** for the `main` branch
3. Configure the following settings:

#### ✅ **Required Settings**
- **Branch name pattern**: `main`
- **Require a pull request before merging**: ✅
  - **Require approvals**: 2 (minimum)
  - **Dismiss stale PR approvals when new commits are pushed**: ✅
  - **Require review from code owners**: ✅
- **Require status checks to pass before merging**: ✅
  - **Require branches to be up to date before merging**: ✅
  - **Status checks that are required**:
    - `build_project` (from GitHub Actions)
    - `security_scan` (from GitHub Actions)
    - `dependency_check` (from GitHub Actions)
- **Require conversation resolution before merging**: ✅
- **Require signed commits**: ✅
- **Require linear history**: ✅
- **Include administrators**: ✅

#### 🔒 **Additional Security Settings**
- **Restrict pushes that create files that override GitHub's default file protection**: ✅
- **Require deployments to succeed before merging**: ✅
- **Lock branch**: ❌ (allows emergency fixes)

### Develop Branch Protection
1. Create a similar rule for the `develop` branch
2. Use the same settings as main, but with 1 required approval instead of 2

## Repository Security Settings

### Actions and Workflows
1. Go to **Settings** → **Actions** → **General**
2. Configure:
   - **Workflow permissions**: "Read and write permissions"
   - **Allow GitHub Actions to create and approve pull requests**: ❌
   - **Allow GitHub Actions to create and approve pull requests**: ❌

### Security and Analysis
1. Go to **Settings** → **Security and analysis**
2. Enable:
   - **Dependabot alerts**: ✅
   - **Dependabot security updates**: ✅
   - **Dependabot version updates**: ✅
   - **Secret scanning**: ✅
   - **Secret scanning push protection**: ✅
   - **Code scanning**: ✅
   - **Dependency review**: ✅

### Code Security and Analysis
1. Go to **Settings** → **Code security and analysis**
2. Enable:
   - **Code scanning**: ✅
   - **Dependency review**: ✅
   - **Secret scanning**: ✅

## Required Status Checks

The following status checks must pass before merging:

### Build Checks
- `build_project` - Main project build
- `check_imported` - Import verification

### Security Checks
- `security_scan` - Trivy vulnerability scanning
- `dependency_check` - Dependency vulnerability check

### Quality Checks
- `ci` - General CI checks (if enabled)

## Code Owner Configuration

Create `.github/CODEOWNERS` file:

```markdown
# Global code owners
* @fraware

# Security-critical files
SECURITY.md @fraware
.github/workflows/ @fraware
.github/dependabot.yml @fraware

# Lean code
ArkLib/ @fraware
*.lean @fraware

# Documentation
blueprint/ @fraware
README.md @fraware
```

## Security Team Configuration

### Required Reviewers
- **Security Lead**: @fraware
- **Cryptographic Review**: @fraware (until specialized team is formed)
- **Build Security**: @fraware (until specialized team is formed)

### Emergency Access
- **Repository Administrators**: @fraware
- **Emergency Contact**: [TBD]

## Implementation Checklist

### Phase 1: Basic Protection
- [ ] Enable branch protection for `main`
- [ ] Enable branch protection for `develop`
- [ ] Configure required status checks
- [ ] Enable Dependabot alerts

### Phase 2: Enhanced Security
- [ ] Enable secret scanning
- [ ] Enable code scanning
- [ ] Configure CODEOWNERS
- [ ] Enable signed commits requirement

### Phase 3: Advanced Security
- [ ] Enable deployment protection
- [ ] Configure emergency access procedures
- [ ] Set up security team notifications
- [ ] Enable advanced scanning features

## Monitoring and Maintenance

### Weekly Security Review
- Review Dependabot alerts
- Check security scan results
- Verify branch protection compliance
- Update security team contacts

### Monthly Security Audit
- Review access permissions
- Audit workflow security
- Verify dependency security
- Update security policies

## Emergency Procedures

### Security Incident Response
1. **Immediate Action**: Lock affected branches
2. **Investigation**: Review logs and access
3. **Containment**: Remove compromised code
4. **Recovery**: Restore from secure state
5. **Post-Incident**: Document lessons learned

### Emergency Access
- **Who**: Repository administrators only
- **When**: Security incidents only
- **How**: Temporary branch protection bypass
- **Documentation**: Required for all emergency actions

---

*This guide should be reviewed and updated monthly to ensure compliance with security best practices.*
