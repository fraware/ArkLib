# Quick Start Implementation Guide
## ArkLib Security & Infrastructure Fixes

This guide provides **step-by-step instructions** to implement the focused security fixes in **Week 1**.

---

## 🚀 **Day 1-2: GitHub Actions Security Hardening**

### **Step 1: Replace Current Workflow**
```bash
# Backup current workflow
cp .github/workflows/blueprint.yml .github/workflows/blueprint.yml.backup

# Replace with hardened version
cp .github/workflows/blueprint-hardened.yml .github/workflows/blueprint.yml
```

### **Step 2: Configure Repository Settings**
**In GitHub Repository Settings:**

1. **Go to**: `Settings` → `Branches`
2. **Add rule** for `main` branch:
   - ✅ Require a pull request before merging
   - ✅ Require status checks to pass before merging
   - ✅ Require branches to be up to date before merging
   - ✅ Include administrators
3. **Status checks to require**:
   - `ci` (from workflow)
   - `security-scan` (from workflow)
   - `dependency-check` (from workflow)

### **Step 3: Test Security Scanning**
```bash
# Push changes to trigger workflow
git add .github/workflows/blueprint.yml
git commit -m "🔒 Harden GitHub Actions workflow with security scanning"
git push origin main
```

**Expected Result**: New workflow runs with security scanning jobs

---

## 📦 **Day 3-4: Dependency Security Updates**

### **Step 1: Replace Dependabot Configuration**
```bash
# Backup current config
cp .github/dependabot.yml .github/dependabot.yml.backup

# Replace with enhanced version
cp .github/dependabot-enhanced.yml .github/dependabot.yml
```

### **Step 2: Update Ruby Dependencies**
```bash
cd home_page

# Update vulnerable gems
bundle update activesupport
bundle update github-pages
bundle update

# Verify updates
bundle list | grep -E "(activesupport|github-pages)"
```

**Expected Result**: `activesupport` and `github-pages` updated to latest versions

### **Step 3: Test Website Functionality**
```bash
# Test Jekyll build
bundle exec jekyll build

# Verify no errors
echo "Build successful if no errors above"
```

---

## 🛠️ **Day 5-7: Lean Toolchain Research & Planning**

### **Step 1: Research Latest Lean Version**
```bash
# Check current version
cat lean-toolchain

# Research latest stable version
# Visit: https://github.com/leanprover/lean4/releases
# Look for latest stable release (e.g., 4.19.0)
```

### **Step 2: Test Compatibility**
```bash
# Create test branch
git checkout -b test-lean-upgrade

# Update lean-toolchain temporarily
echo "leanprover/lean4:v4.19.0" > lean-toolchain

# Test build
lake build

# If successful, commit changes
git add lean-toolchain
git commit -m "🛠️ Upgrade Lean to v4.19.0"
git push origin test-lean-upgrade
```

### **Step 3: Plan Production Upgrade**
- [ ] **If test successful**: Plan production upgrade
- [ ] **If test fails**: Document compatibility issues
- [ ] **Create rollback plan**: Keep current version as fallback

---

## ✅ **Verification Checklist**

### **GitHub Actions Security**
- [ ] Workflow replaced with hardened version
- [ ] Security scanning jobs running
- [ ] Branch protection rules enabled
- [ ] Status checks required

### **Dependency Security**
- [ ] Dependabot config replaced
- [ ] Ruby gems updated
- [ ] Website builds successfully
- [ ] Security patches automated

### **Lean Toolchain**
- [ ] Latest version researched
- [ ] Compatibility tested
- [ ] Upgrade plan documented
- [ ] Rollback strategy ready

---

## 🚨 **Troubleshooting Common Issues**

### **Workflow Failures**
```bash
# Check workflow logs
# Go to: Actions tab → Latest workflow run → View logs

# Common fixes:
# 1. Ensure all actions are pinned to SHAs
# 2. Verify permissions are correct
# 3. Check branch protection settings
```

### **Dependency Conflicts**
```bash
# If bundle update fails
bundle update --conservative

# If specific gem fails
bundle update --source gem_name

# Check for version conflicts
bundle check
```

### **Build Failures**
```bash
# Clean and rebuild
lake clean
lake build

# Check Lean version compatibility
lake --version
```

---

## 📊 **Success Metrics - Week 1**

By the end of Week 1, you should achieve:

- [ ] **80% reduction** in infrastructure security vulnerabilities
- [ ] **Automated security scanning** in CI/CD pipeline
- [ ] **Enhanced Dependabot** for ongoing security maintenance
- [ ] **Clear upgrade path** for Lean toolchain

---

## 🎯 **Next Week Preview**

**Week 2 Focus:**
- Complete any remaining configuration
- Validate all security measures
- Document procedures for team
- Begin performance testing

---

*This guide provides immediate, actionable steps to secure your infrastructure. Each step can be completed in 1-2 hours, with full implementation achievable within one week.*
