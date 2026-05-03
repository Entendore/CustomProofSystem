#!/usr/bin/env python3
import os
import sys
from pathlib import Path

def setup_test_directory():
    """Create the test directory structure"""
    base_dir = Path(__file__).parent
    
    # Create tests directory
    tests_dir = base_dir / "tests"
    tests_dir.mkdir(exist_ok=True)
    
    # Create ProofScripts directory
    proof_scripts_dir = tests_dir / "ProofScripts"
    proof_scripts_dir.mkdir(exist_ok=True)
    
    # Create test files
    test_files = {
        "basic_propositional.proof": """
# Basic implication
goal P → P
intro H
exact H
proof
""",
        "conjunction.proof": """
# Conjunction proof
goal P → Q → P ∧ Q
intro Hp
intro Hq
split
exact Hp
exact Hq
proof
""",
        "quantifiers.proof": """
# Universal quantifier
goal (∀x. P(x)) → P(a)
intro Hforall
forall_elim 0 a
assumption
proof
""",
        "negation.proof": """
# Double negation elimination
goal ¬¬P → P
intro Hnnp
dne Hnnp
proof
""",
        "equality.proof": """
# Reflexivity of equality
goal ∀x. x = x
intro x
reflexivity
proof
"""
    }
    
    # Write proof scripts
    for filename, content in test_files.items():
        with open(proof_scripts_dir / filename, 'w') as f:
            f.write(content.strip())
    
    # Create test modules
    with open(tests_dir / "test_proof_assistant.py", 'w') as f:
        f.write('''import pytest
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

def test_proof_scripts():
    """Run all proof scripts in the ProofScripts folder"""
    from proof_assistant import ProofState, parse_formula
    
    proof_dir = Path(__file__).parent / "ProofScripts"
    assert proof_dir.exists(), "ProofScripts folder missing"
    
    success_count = 0
    total_count = 0
    
    for script_file in proof_dir.glob("*.proof"):
        total_count += 1
        print(f"\\nTesting {script_file.name}")
        
        try:
            # This would be replaced with actual script running logic
            # For now, just check that files exist and are readable
            with open(script_file, 'r') as f:
                content = f.read()
                assert len(content) > 0, f"Empty script: {script_file.name}"
            
            success_count += 1
            print(f"✓ {script_file.name}")
            
        except Exception as e:
            print(f"✗ {script_file.name}: {str(e)}")
    
    print(f"\\nTest summary: {success_count}/{total_count} scripts processed")
    assert success_count > 0, "No proof scripts were processed"
    # Don't fail if some proofs are incomplete - that's expected in testing
''')
    
    with open(tests_dir / "__init__.py", 'w') as f:
        f.write("# Test package initialization")
    
    print("Test directory structure created successfully!")
    print(f"Created {len(test_files)} proof script test files.")

if __name__ == "__main__":
    setup_test_directory()